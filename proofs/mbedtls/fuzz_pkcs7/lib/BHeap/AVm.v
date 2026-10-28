(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Madvise.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AJ.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Local Ltac Stdlib.micromega.Lia.nia ::= nia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrcAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia_ah. (* [comment removed for export] *)
Ltac2 gd_tbl_AVm () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Datatypes.fst"; "Corelib.Numbers.BinNums.Z"; "ARUN_1.v_stk"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.snd"; "ARUN_1.v_img"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.hull64"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "Corelib.Init.Logic.ex"; "ARUN_1.trange"; "Stdlib.Lists.List.In"; "ARUN_1.v_tr"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "ARUN_1.t_cs"; "Corelib.Init.Datatypes.true"; "ARUN_1.t_lo"; "ARUN_1.t_hi"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.map"; "ARUN_1.t_len"; "Stdlib.Lists.List.filter"; "ARUN_1.v_ghost"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "ARUN_1.AVm.zpb"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.shadow_of"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.orb"; "Stdlib.Lists.List.existsb"; "ARUN_1.AVm.pg_shadow_b"; "ARUN_1.AVm.csranges"; "ARUN_1.AVm.pg_inside_b"; "ARUN_1.AVm.lazyranges"; "Corelib.Lists.ListDef.Forall"; "ARUN_1.AVm.tfacts"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.AHeap.AVmLib.covers"; "ARUN_1.v_unit"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.ncov"; "ARUN_1.t_lit"; "ARUN_1.v_hulls"; "Stdlib.Lists.List.NoDup"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "ARUN_1.lkind"; "ARUN_1.t_kind"; "ARUN_1.KNoacc"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "Corelib.Init.Datatypes.false"; "ARUN_1.KEager"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.v_eb"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.bottomup_floor"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL_MIN"; "ARUN_1.v_cover"; "RocqVerifyHarness.AgentSubmission.AHeap.AFreeSlot.zsum"; "RocqVerifyHarness.AgentSubmission.AHeap.AFreeSlot.rhits"; "ARUN_1.v_cb20"; "ARUN_1.v_cb23"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "ARUN_1.AVm.vgood"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.aok_addr"; "ARUN_1.AVm.vcs"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_lazy"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "ARUN_1.AVm.VLIMIT"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.eager_bytes"; "Stdlib.ZArith.BinInt.Z.mul"; "ARUN_1.AVm.vnb"; "RocqVerifyHarness.AgentSubmission.ABoot.BackingAlgebra.model_ivs_wf"; "ARUN_1.AVm.vm_table"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "ARUN_1.AVm.vcensus"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "ARUN_1.AVm.vwf"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.atop_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "Corelib.Init.Datatypes.list"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.div"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "ARUN_1.AVm.npages_shadow"; "ARUN_1.AVm.npages_inside"; "ARUN_1.vst"; "ARUN_1.AVm.vranges_ok"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.AVm.HKv"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.mo_mat"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "RocqVerifyHarness.AgentSubmission.ABoot.BackingAlgebra.sum_count"; "Corelib.Init.Datatypes.negb"; "RocqVerifyHarness.AgentSubmission.ABoot.BackingAlgebra.covered"; "RocqVerifyHarness.AgentSubmission.AHeap.AVmLib.clear"; "RocqVerifyHarness.AgentSubmission.ABoot.BackingAlgebra.ivs_wf"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "ARUN_1.VST"; "ARUN_1.TR"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.AVm.v_add_eager"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "ARUN_1.KLazy"; "ARUN_1.AVm.v_add_lazy"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.anon_grantable"; "ARUN_1.AVm.J20"; "ARUN_1.AVm.J23"; "RocqVerifyHarness.AgentSubmission.ABoot.BackingAlgebra.overlap_sum"; "ARUN_1.AVm.v_add_sub"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_commit"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "RocqVerifyHarness.AgentSubmission.AHeap.ASysS.fixrw_grantable"; "RocqVerifyHarness.AgentSubmission.ABoot.BackingAlgebra.B"; "RocqVerifyHarness.AgentSubmission.ABoot.BackingAlgebra.S"; "ARUN_1.AVm.v_remove"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.munmap_model"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_ok"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Madvise.madvise_dontneed_next"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "Stdlib.Sorting.Permutation.Permutation"; "LinuxProcessSemantics.LinuxProcessSem.State.iv_subtract"; "RocqVerifyHarness.AgentSubmission.BHeap.AJ.msep"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.fixrw_destroyed"; "ARUN_1.AVm.v_hole"; "ARUN_1.AVm.HKh"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.norep_grant"].

Section ARUN_1. Context {hAR : arun}.
Inductive lkind := KEager | KLazy | KNoacc.

Record trange := TR { t_lo : Z; t_len : Z; t_kind : lkind; t_lit : bool; t_cs : bool }.
(* [comment removed for export] *)

Record vst := VST {
  v_tr : list trange;       (* [comment removed for export] *)
  v_hulls : list (Z * Z);   (* [comment removed for export] *)
  v_ghost : list (Z * Z);   (* [comment removed for export] *)
  v_stk : Z * Z;            (* [comment removed for export] *)
  v_img : Z * Z;            (* [comment removed for export] *)
  v_eb : Z;                 (* [comment removed for export] *)
  v_cover : list (Z * Z);   (* [comment removed for export] *)
  v_cb20 : Z; v_cb23 : Z;   (* [comment removed for export] *)
  v_unit : Z -> Z -> Prop   (* [comment removed for export] *)
}.

Definition t_hi (t : trange) : Z := t_lo t + t_len t.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L38796341010.7L40893227604.7L42856110042.9L53384298520.8L551690872.8  L61028844156.5L61035166413.3L63368128237.600000500=00H00M00U00Z00]00bS1g1qS1g1q2MqS1g1q2E12E2S1g1qS1g1q2MqS1g1qS1gS1g1q". (* [comment removed for export] *)
#[using="Type"] Lemma hull64_al8 : forall g, g mod 8 = 0 -> hull64 (g + 7) = hull64 g.
Proof.
  intros g G. unfold hull64.
  pose proof (Z.div_mod g 8 ltac:(lia)) as D8. rewrite G, Z.add_0_r in D8.
  set (q := g / 8) in D8.
  pose proof (Z.div_mod q 8 ltac:(lia)) as Dq. pose proof (Z.mod_pos_bound q 8 ltac:(lia)) as Mq.
  assert (E1 : g mod 64 = 8 * (q mod 8)).
  { rewrite D8. rewrite Dq at 1. replace (8 * (8 * (q / 8) + q mod 8)) with (8 * (q mod 8) + (q / 8) * 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  assert (E2 : (g + 7) mod 64 = 8 * (q mod 8) + 7).
  { rewrite D8. rewrite Dq at 1. replace (8 * (8 * (q / 8) + q mod 8) + 7) with ((8 * (q mod 8) + 7) + (q / 8) * 64) by lia.
    rewrite Z_mod_plus_full. apply Z.mod_small. lia. }
  lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Section AVm.
Variable AL : asan_layout.

(* [comment removed for export] *)
Definition vcs (v : vst) (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(0.(1.(2.(3.$4.$4.(5.O2.))O1.)(6.O1.(7.$4.$4.(5.O2.))))(0.(1.(1.(2.(3.$4.$4.(8.O2.))O1.)(6.O1.(7.$4.$4.(8.O2.))))(1.(9.(1.(2.(:.(;.VAL,))O1.)(6.O1.(<.(:.(<.(;.VAL,)+7.))+40.))))(9.(1.(2.(:.(=.VAL,))O1.)(6.O1.(<.(:.(<.(=.VAL,)+7.))+40.))))))(>.$?.Lt,$?.(1.(10.$?.R1.(11.O2.))(1.(12.$13.(14.R1.)$15.)(1.(2.(16.R1.)O1.)(6.O1.(17.R1.))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition csranges (v : vst) : list (Z * Z) := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(18.(19.$4.$4.)(1:.$4.$4.(3.$4.$4.(5.O1.))(1;.(7.$4.$4.(5.O1.))(3.$4.$4.(5.O1.))))(18.(19.$4.$4.)(1:.$4.$4.(3.$4.$4.(8.O1.))(1;.(7.$4.$4.(8.O1.))(3.$4.$4.(8.O1.))))(1<.(19.$4.$4.)(1=.$?.(19.$4.$4.)Lt,$?.(1:.$4.$4.(16.R1.)(1>.R1.))(1?.$?.$14.(11.O1.)))(20.O1.))))")
(* [comment removed for export] *).

Definition is_lazy_cs (t : trange) : bool := match t_kind t with KLazy => t_cs t | _ => false end.
Definition lazyranges (v : vst) : list (Z * Z) :=
  map (fun t => (t_lo t, t_len t)) (List.filter is_lazy_cs (v_tr v)).

(* [comment removed for export] *)
Definition zpb (z : Z) : Z := z / 4096 * 4096.
Definition pg_shadow_b (r : Z * Z) (p : word) : bool := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(21.(21.(22.(23.(24.VAL,(3.$4.$4.O2.)))(25.&40.O1.))(22.(25.&40.O1.)(23.(24.VAL,(1;.(<.(3.$4.$4.O2.)(7.$4.$4.O2.))+1.)))))(26.(27.(25.&40.O1.)+1000.)=))")
(* [comment removed for export] *).
Definition pg_inside_b (r : Z * Z) (p : word) : bool := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(21.(21.(22.(3.$4.$4.O2.)(25.&40.O1.))(22.(<.(25.&40.O1.)+1000.)(<.(3.$4.$4.O2.)(7.$4.$4.O2.))))(26.(27.(25.&40.O1.)+1000.)=))")
(* [comment removed for export] *).

Definition vgood_b (v : vst) (p : word) : bool := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(28.(29.(19.$4.$4.)Lr,(19.$4.$4.)(2:.R1.O1.)(2;.O2.))(29.(19.$4.$4.)Lr,(19.$4.$4.)(2<.R1.O1.)(2=.O2.)))")
(* [comment removed for export] *).
Definition vgood (v : vst) (p : word) : Prop := vgood_b v p = true.

(* [comment removed for export] *)
Definition npages_shadow (r : Z * Z) : Z := snd r / 32768 + 3.
Definition npages_inside (r : Z * Z) : Z := snd r / 4096 + 1.
Definition vnb (v : vst) : Z := zsum npages_shadow (csranges v) + zsum npages_inside (lazyranges v).

(* [comment removed for export] *)
Definition tfacts (M N Lz : list (word * word)) (t : trange) : Prop :=
  covers M (t_lo t) (t_hi t)
  /\ (t_lit t = true -> haslit M (t_lo t) (t_len t))
  /\ match t_kind t with
     | KEager => clear N (t_lo t) (t_hi t) /\ clear Lz (t_lo t) (t_hi t)
     | KLazy  => clear N (t_lo t) (t_hi t)
     | KNoacc => True   (* [comment removed for export] *)
     end.

Definition vm_table (v : vst) (M N Lz : list (word * word)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(1.(2>.$?.(2?.O3.O2.O1.)(11.O4.))(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.O2.)(31.O3.(25.&40.(3.(30.&40.)(30.&40.)R2.))(<.(25.&40.(3.(30.&40.)(30.&40.)R2.))(25.&40.(7.(30.&40.)(30.&40.)R2.))))(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.O1.)(31.O3.(25.&40.(3.(30.&40.)(30.&40.)R2.))(<.(25.&40.(3.(30.&40.)(30.&40.)R2.))(25.&40.(7.(30.&40.)(30.&40.)R2.))))(1.PU,$4.Pn,$4.P,(32.O4.R2.R1.)(31.O3.R3.(<.R3.R2.))(1.(1.PU,$4.Pn,$4.P,(32.O4.R2.R1.)P,Pt,$?.P,(10.$?.R1.(11.O4.))(0.(2.(<.R5.R4.)(16.R2.))(2.(17.R2.)R5.))Px,$4.P,(1.(2.R5.R1.)(6.R1.(<.R5.R4.)))(33.O2.R2.)(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.O3.)(6.=(25.&40.(7.(30.&40.)(30.&40.)R2.)))(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.O1.)Px,$4.P,(1.(2.(25.&40.(3.(30.&40.)(30.&40.)R3.))R1.)(6.R1.(<.(25.&40.(3.(30.&40.)(30.&40.)R3.))(25.&40.(7.(30.&40.)(30.&40.)R3.)))))(0.(>.$?.Lt,$?.(1.(10.$?.R1.(11.O4.))(1.(12.$13.(34.R1.)$15.)(1.(2.(16.R1.)R3.)(6.R3.(17.R1.))))))(>.$4.LU,$4.(>.$4.Ln,$4.(1.(32.O4.R2.R1.)(1.(2.R2.R4.)(6.R4.(<.R2.R1.)))))))(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.O3.)Px,$4.P,(1.(2.(25.&40.(3.(30.&40.)(30.&40.)R3.))R1.)(6.R1.(<.(25.&40.(3.(30.&40.)(30.&40.)R3.))(25.&40.(7.(30.&40.)(30.&40.)R3.)))))(0.(>.$?.Lt,$?.(1.(10.$?.R1.(11.O4.))(1.(12.$13.(34.R1.)$15.)(1.(2.(16.R1.)R3.)(6.R3.(17.R1.))))))(>.$4.LU,$4.(>.$4.Ln,$4.(1.(32.O4.R2.R1.)(1.(2.R2.R4.)(6.R4.(<.R2.R1.)))))))Pe,(19.(30.&40.)(30.&40.))PH,(19.$4.$4.)P,(10.(19.(30.&40.)(30.&40.))R2.O3.)P,(10.(19.$4.$4.)R2.(35.O4.))P,(6.(25.&40.(3.(30.&40.)(30.&40.)R4.))(<.(3.$4.$4.R3.)(7.$4.$4.R3.)))P,(6.(3.$4.$4.R4.)(<.(25.&40.(3.(30.&40.)(30.&40.)R5.))(25.&40.(7.(30.&40.)(30.&40.)R5.))))(1.(2.(3.$4.$4.R5.)(25.&40.(3.(30.&40.)(30.&40.)R6.)))(2.(<.(25.&40.(3.(30.&40.)(30.&40.)R6.))(25.&40.(7.(30.&40.)(30.&40.)R6.)))(<.(3.$4.$4.R5.)(7.$4.$4.R5.))))))))(1.(36.(19.(30.&40.)(30.&40.))O3.)(1.Pe1,(19.(30.&40.)(30.&40.))Pe2,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R2.O3.)P,(10.(19.(30.&40.)(30.&40.))R2.O3.)(0.(12.(19.(30.&40.)(30.&40.))R4.R3.)(0.(2.(<.(25.&40.(3.(30.&40.)(30.&40.)R4.))(25.&40.(7.(30.&40.)(30.&40.)R4.)))(25.&40.(3.(30.&40.)(30.&40.)R3.)))(2.(<.(25.&40.(3.(30.&40.)(30.&40.)R3.))(25.&40.(7.(30.&40.)(30.&40.)R3.)))(25.&40.(3.(30.&40.)(30.&40.)R4.)))))(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.O2.)(6.=(25.&40.(7.(30.&40.)(30.&40.)R2.)))(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.O1.)(6.=(25.&40.(7.(30.&40.)(30.&40.)R2.)))(1.(31.O3.+7???7000.+8???7000.)(1.(31.O3.+8???7000.+2008???7000.)(31.O3.+2008???7000.+10007???8000.))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition vwf (v : vst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(1.(2>.$?.Lt,$?.(1.(2.+1000.(16.R1.))(1.(6.=(1>.R1.))(1.(2.(17.R1.)(37.VhAR,))(1.(12.$4.(27.(16.R1.)+1000.)=)(1.(12.$4.(27.(1>.R1.)+1000.)=)(1.P,(12.$13.(14.R1.)$15.)(9.(12.$38.(39.R2.)$3:.))(0.(2.(17.R1.)(3;.VAL,))(2.(3<.VAL,)(16.R1.)))))))))(11.O1.))(1.Pt1,$?.Pt2,$?.P,(10.$?.R2.(11.O1.))P,(10.$?.R2.(11.O1.))(0.(12.$?.R4.R3.)(0.(2.(17.R4.)(16.R3.))(2.(17.R3.)(16.R4.))))(1.(2>.(19.$4.$4.)LH,(19.$4.$4.)(1.(2.+1000.(3.$4.$4.R1.))(1.(6.=(7.$4.$4.R1.))(1.(2.(<.(3.$4.$4.R1.)(7.$4.$4.R1.))(37.VhAR,))(1.(12.$4.(27.(3.$4.$4.R1.)+1000.)=)(1.(12.$4.(27.(7.$4.$4.R1.)+1000.)=)(0.(2.(<.(3.$4.$4.R1.)(7.$4.$4.R1.))+7???7000.)(2.+10007???8000.(3.$4.$4.R1.))))))))(35.O1.))(1.PH1,(19.$4.$4.)PH2,(19.$4.$4.)P,(10.(19.$4.$4.)R2.(35.O1.))P,(10.(19.$4.$4.)R2.(35.O1.))(0.(12.(19.$4.$4.)R4.R3.)(0.(2.(<.(3.$4.$4.R4.)(7.$4.$4.R4.))(3.$4.$4.R3.))(2.(<.(3.$4.$4.R3.)(7.$4.$4.R3.))(3.$4.$4.R4.))))(1.Pt,$?.PH,(19.$4.$4.)P,(10.$?.R2.(11.O1.))P,(10.(19.$4.$4.)R2.(35.O1.))(0.(1.(2.(3.$4.$4.R3.)(16.R4.))(1.(2.(17.R4.)(<.(3.$4.$4.R3.)(7.$4.$4.R3.)))(1.(12.$13.(34.R4.)$3=.)(12.$38.(39.R4.)$3>.))))(0.(2.(17.R4.)(3.$4.$4.R3.))(2.(<.(3.$4.$4.R3.)(7.$4.$4.R3.))(16.R4.))))(1.(2.(37.VhAR,)(3.$4.$4.(5.O1.)))(1.(2.(3.$4.$4.(5.O1.))(7.$4.$4.(5.O1.)))(1.(2.(7.$4.$4.(5.O1.))(3?.+2.+2?.))(1.(12.$4.(3.$4.$4.(8.O1.))(3;.VAL,))(1.(12.$4.(7.$4.$4.(8.O1.))(3<.VAL,))(1.(2.=(3;.VAL,))(1.(2.(3;.VAL,)(3<.VAL,))(1.(2.(3<.VAL,)(37.VhAR,))(1.(2>.(19.$4.$4.)Lr,(19.$4.$4.)(1.(2.=(3.$4.$4.R1.))(1.(2.=(7.$4.$4.R1.))(2.(<.(3.$4.$4.R1.)(7.$4.$4.R1.))(3?.+2.+2?.))))(20.O1.))(1.Pt,$?.P,(10.$?.R1.(11.O1.))P,(12.$13.(14.R2.)$15.)(0.(2.(17.R3.)+7???7000.)(2.+10007???8000.(16.R3.)))(1.(2.=(40.O1.))(1.(36.$?.(11.O1.))(1.PU,$4.Pn,$4.P,(32.O1.R2.R1.)(1.(6.=R2.)(1.(2.+1000.R3.)(1.(2.(<.R3.R2.)(37.VhAR,))(1.(12.$4.(27.R3.+1000.)=)(12.$4.(27.R2.+1000.)=)))))(1.PU,$4.Pn,$4.PU',$4.Pn',$4.P,(32.O1.R4.R3.)P,(32.O1.R3.R2.)(0.(1.(12.$4.R6.R4.)(12.$4.R5.R3.))(0.(2.(<.R6.R5.)R4.)(2.(<.R4.R3.)R6.)))(1.PH,(19.$4.$4.)P,(10.(19.$4.$4.)R1.(35.O1.))Px,$4.P,(1.(2.(3.$4.$4.R3.)R1.)(6.R1.(<.(3.$4.$4.R3.)(7.$4.$4.R3.))))(>.$4.LU,$4.(>.$4.Ln,$4.(1.(32.O1.R2.R1.)(1.(2.R2.R4.)(6.R4.(<.R2.R1.))))))Pt,$?.PU,$4.Pn,$4.P,(10.$?.R3.(11.O1.))P,(12.$13.(34.R4.)$15.)P,(32.O1.R4.R3.)(0.(2.(<.R5.R4.)(16.R6.))(2.(17.R6.)R5.))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)  (* [comment removed for export] *)
Definition vcensus (v : vst) (R M : list (word * word)) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.(1<.(19.(30.&40.)(30.&40.))O2.O1.))P,(6.$41.(<.(25.&40.(3.(30.&40.)(30.&40.)R2.))(25.&40.(7.(30.&40.)(30.&40.)R2.))))P,(6.(25.&40.(3.(30.&40.)(30.&40.)R3.))$42.)(>.(19.$4.$4.)Lc,(19.$4.$4.)(1.(10.(19.$4.$4.)R1.(43.O3.))(1.(2.(3.$4.$4.R1.)(25.&40.(3.(30.&40.)(30.&40.)R5.)))(2.(<.(25.&40.(3.(30.&40.)(30.&40.)R5.))(25.&40.(7.(30.&40.)(30.&40.)R5.)))(<.(3.$4.$4.R1.)(7.$4.$4.R1.))))))(1.Pc,(19.$4.$4.)P,(10.(19.$4.$4.)R1.(43.O3.))(2.=(7.$4.$4.R2.))(1.(2.(44.(19.$4.$4.)(45.$41.(3?.+2.+14.)(1;.$42.$41.))(43.O3.))(46.O3.))(2.(44.(19.$4.$4.)(45.$41.(3?.+2.+17.)(1;.$42.$41.))(43.O3.))(47.O3.)))))")
(* [comment removed for export] *).  (* [comment removed for export] *)

Definition VLIMIT : Z := 0x8000000000.   (* [comment removed for export] *)

Definition HKv (v : vst) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(1.(12.(48.(30.&40.))(49.O1.)(4:.(30.&40.)))(1.(36.(30.&40.)(4;.O1.))(1.(2>.(30.&40.)(4<.O2.)(4;.O1.))(1.Px,$4.P,(4=.VAL,(4>.O2.)R1.)P,(12.$13.(4?.(50.R2.)(51.O1.))$15.)(4<.O2.(50.R3.))(1.(12.$4.(52.(53.O1.))$54.)(1.(2.(55.O1.)(40.O2.))(1.(2.(<.(40.O2.)(56.+1000.(57.O2.)))$54.)(1.(58.O1.)(1.(59.O2.(5:.(53.O1.))(5;.(53.O1.))(51.O1.))(1.(5<.O2.(5=.(53.O1.))(5:.(53.O1.)))(1.Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.(5=.(53.O1.)))(1.(2.(3;.VAL,)(25.&40.(3.(30.&40.)(30.&40.)R2.)))(2.(<.(25.&40.(3.(30.&40.)(30.&40.)R2.))(25.&40.(7.(30.&40.)(30.&40.)R2.)))(3<.VAL,)))(1.Px,$4.P,(1.(2.(3;.VAL,)R1.)(6.R1.(3<.VAL,)))(>.(19.(30.&40.)(30.&40.))Le,(19.(30.&40.)(30.&40.))(1.(10.(19.(30.&40.)(30.&40.))R1.(5=.(53.O1.)))(1.(2.(25.&40.(3.(30.&40.)(30.&40.)R1.))R3.)(6.R3.(<.(25.&40.(3.(30.&40.)(30.&40.)R1.))(25.&40.(7.(30.&40.)(30.&40.)R1.)))))))(1.(5>.O2.)(5?.VhAR,(60.(53.O1.))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L36723957613.7L52169880231.700000:00DS1A1f1r2IHS1A1f1r2IH". (* [comment removed for export] *)
#[using="Type"] Lemma filter_partition_length : forall {A} (f : A -> bool) (l : list A),
  (length l = length (List.filter f l) + length (List.filter (fun x => negb (f x)) l))%nat.
Proof. intros A f l. induction l as [|x r IH]; cbn; [reflexivity|]. destruct (f x); cbn; lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020>L2497101157.13L48557147668.700000D00ES2pb2nb1r2rs1l2L12L2S". (* [comment removed for export] *)
#[using="Type"] Lemma card_ranges : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Ppb,P,(19.$4.$4.)P,(30.&40.)$13.Pnb,P,(19.$4.$4.)$4.Prs,(61.(19.$4.$4.))P,Pr,(19.$4.$4.)Pl',(61.(30.&40.))P,(10.(19.$4.$4.)R2.R3.)P,(36.(30.&40.)R2.)P,(2>.(30.&40.)Lp,(30.&40.)(12.$13.A2.R8.R5.R1.$15.)R3.)(2.(62.(63.(30.&40.)R4.))A1.R7.R5.)Pl,(61.(30.&40.))P,(36.(30.&40.)R1.)P,(2>.(30.&40.)Lp,(30.&40.)(12.$13.(29.(19.$4.$4.)Lr,(19.$4.$4.)A2.R8.R1.R2.R5.)$15.)R2.)(2.(62.(63.(30.&40.)R3.))(44.(19.$4.$4.)R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros pb nb rs. induction rs as [|r rs IH]; intros BND l ND ALL.
  - cbn. destruct l as [|p l']; [cbn; lia|]. exfalso. pose proof (proj1 (Forall_forall _ _) ALL p ltac:(now left)) as X. cbn in X. discriminate.
  - cbn [zsum].
    rewrite (filter_partition_length (pb r) l).
    assert (L1 : Z.of_nat (length (List.filter (pb r) l)) <= nb r).
    { apply BND; [now left| apply NoDup_filter; exact ND|]. apply Forall_forall. intros p Hp. apply filter_In in Hp. exact (proj2 Hp). }
    assert (L2 : Z.of_nat (length (List.filter (fun x => negb (pb r x)) l)) <= zsum nb rs).
    { apply IH.
      - intros r' l' Hr' ND' F'. apply BND; [now right| exact ND'| exact F'].
      - apply NoDup_filter. exact ND.
      - apply Forall_forall. intros p Hp. apply filter_In in Hp. destruct Hp as [Hp Hn].
        pose proof (proj1 (Forall_forall _ _) ALL p Hp) as X. cbn [existsb] in X.
        destruct (pb r p); [discriminate| exact X]. }
    rewrite Nat2Z.inj_add. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L39845871493.10L43373901463.1400000:00IS2lo2hi2LHS2lo2hi1p2H02H1". (* [comment removed for export] *)
#[using="Type"] Lemma NoDup_words_interval : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pl,(61.(30.&40.))Plo,$4.Phi,$4.P,(36.(30.&40.)R3.)P,Pp,(30.&40.)P,(10.(30.&40.)R1.R5.)(1.(1.(2.R5.(25.&40.R2.))(2.(25.&40.R2.)R4.))(12.$4.(27.(25.&40.R2.)+1000.)=))P,(2.R4.(<.R3.+1.))(2.(62.(63.(30.&40.)R6.))(<.(64.(1;.(<.R4.+1.)R5.)+1000.)+1.))")
(* [comment removed for export] *).
Proof.
  intros l lo hi ND H LH.
  assert (NDm : List.NoDup (map (fun p : word => bv_unsigned p) l)).
  { apply NoDup_map_inj_on; [exact ND|]. intros x y _ _ E. apply bv_eq. exact E. }
  pose proof (NoDup_pages_interval (map (fun p : word => bv_unsigned p) l) lo (hi + 1) NDm) as X.
  rewrite length_map in X. unfold page_size in X. apply X; [| lia].
  intros z Hz. apply in_map_iff in Hz. ddestruct Hz as (p & <- & Hp). destruct (H p Hp). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


Local Ltac2 Set LiaOrc.tbl := fun () => "00F0?L10810091493.29L18758831314.13L18926677105.22L18926677232.24L18926677363.29L18928648233.25L18928648491.21L18928648618.23L18928712348.13L18932075069.20L29432502745.12L29784316908.13L43470213452.14L59308841425.17L59360127483.21L61028632438.14L61028698103.16L63368119852.17L63368119981.15L63374458396.12L6658362348.29 L67316559891.1900000T00f01>01V02:02U02m03E03T03l04>04M04_05906706H06Y06j07;07J07n08HS2AL2lo3len2H02H12q12q21u1w2qa2qb2q3S2AL2lo3len2H11A1BS2AL2lo3len2H02q12q21u1wS2AL2lo3len2H02q12q21u1wS2AL2lo3len2H02H12q12q21u1w2qa2qb2q3S2AL2lo3len2H02H12q12q21u1wS2AL2lo3len2H02q12q21u1wS2AL2lo3len2H02q12q21u1wS2AL2lo3len1A1BS2AL2lo3len2H02q12q21u1wS2AL2lo3len2H01A1BS2AL2lo3len1A1BS2AL2lo3len1A1B2ABS2AL2lo3len1p1A1B2AB2X12X2S2AL2lo3len2H02H12q12q22D12M12D22M22qa2D32M32qb2D42M42q32D52M5S2lo3len2H02q12q2S2lo3len2H02q12q2S2lo3len2H02q12q2S2lo3len2H02q12q2S2AL2lo3len1A1BS2AL2lo3len2H02H12q12q21u1w2qa2qb2q3S2AL2lo3len1A1B1p2X12X22X3". (* [comment removed for export] *)
#[using="Type"] Lemma pg_shadow_card : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pr,(19.$4.$4.)Pl',(61.(30.&40.))P,(2.=(65.VAL,))P,(2.=(3.$4.$4.R3.))P,(2.=(7.$4.$4.R4.))P,(36.(30.&40.)R4.)P,(2>.(30.&40.)Lp,(30.&40.)(12.$13.(2:.R7.R1.)$15.)R5.)(2.(62.(63.(30.&40.)R6.))(66.R7.))")
(* [comment removed for export] *).
Proof.
  intros [lo len] l' SB H0 H1 ND F. unfold npages_shadow. cbn [fst snd] in *.
  set (A := zpb (shadow_of AL lo)). set (B := zpb (shadow_of AL (lo + len - 1))).
  assert (SA : 0 <= shadow_of AL lo) by (unfold shadow_of; apply Z.add_nonneg_nonneg; [exact SB| apply Z.div_pos; lia]).
  destruct (Z.le_gt_cases A B) as [AB|AB].
  - eapply Z.le_trans. { apply (NoDup_words_interval l' A B ND); [| lia]. intros p Hp. pose proof (proj1 (Forall_forall _ _) F p Hp) as X.
      unfold pg_shadow_b in X. cbn [fst snd] in X. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
      apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.eqb_eq in X3. fold A in X1. fold B in X2. lia. }
    subst A B. unfold zpb, shadow_of.
    set (q1 := lo / 8). set (q2 := (lo + len - 1) / 8).
    pose proof (Z.div_mod lo 8 ltac:(lia)) as D1. pose proof (Z.mod_pos_bound lo 8 ltac:(lia)) as M1.
    pose proof (Z.div_mod (lo + len - 1) 8 ltac:(lia)) as D2. pose proof (Z.mod_pos_bound (lo + len - 1) 8 ltac:(lia)) as M2.
    fold q1 in D1. fold q2 in D2.
    set (u := al_sb AL + q1). set (w := al_sb AL + q2).
    pose proof (Z.div_mod u 4096 ltac:(lia)) as D3. pose proof (Z.mod_pos_bound u 4096 ltac:(lia)) as M3.
    pose proof (Z.div_mod w 4096 ltac:(lia)) as D4. pose proof (Z.mod_pos_bound w 4096 ltac:(lia)) as M4.
    pose proof (Z.div_mod len 32768 ltac:(lia)) as D5. pose proof (Z.mod_pos_bound len 32768 ltac:(lia)) as M5.
    set (qa := u / 4096) in *. set (qb := w / 4096) in *. set (q3 := len / 32768) in *.
    replace (qb * 4096 + 1 - qa * 4096) with (1 + (qb - qa) * 4096) by lia.
    rewrite Z.div_add, Z.div_small by lia.
    clear - D1 M1 D2 M2 D3 M3 D4 M4 D5 M5 H1 SB H0. subst u w. lia.
  - (* [comment removed for export] *)
    destruct l' as [|p l'']; [cbn; apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]|]. exfalso.
    pose proof (proj1 (Forall_forall _ _) F p ltac:(now left)) as X. unfold pg_shadow_b in X. cbn [fst snd] in X.
    apply andb_prop in X. destruct X as [X _]. apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2.
    fold A in X1. fold B in X2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0090?L13041714502.9 L18930892178.8 L18930892178.9 L28845776619.9 L43374163345.14L45260572683.9 L56905228362.10L59308841425.12L62575253570.9 00000:00;00<00F00Y00^00h01:01BS3len2H11HSSS2lo3len1LS2lo3len1p2X12X22X3S3lenS3len2H11HS2lo3len1p1L2X12X2S2lo3len". (* [comment removed for export] *)
#[using="Type"] Lemma pg_inside_card : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pr,(19.$4.$4.)Pl',(61.(30.&40.))P,(2.=(7.$4.$4.R2.))P,(36.(30.&40.)R2.)P,(2>.(30.&40.)Lp,(30.&40.)(12.$13.(2<.R5.R1.)$15.)R3.)(2.(62.(63.(30.&40.)R4.))(67.R5.))")
(* [comment removed for export] *).
Proof.
  intros [lo len] l' H1 ND F. unfold npages_inside. cbn [fst snd] in *.
  destruct (Z.le_gt_cases 4096 len) as [L|L].
  - eapply Z.le_trans. { apply (NoDup_words_interval l' lo (lo + len - 4096) ND); [| lia]. intros p Hp. pose proof (proj1 (Forall_forall _ _) F p Hp) as X.
      unfold pg_inside_b in X. cbn [fst snd] in X. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
      apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.eqb_eq in X3. lia. }
    replace (lo + len - 4096 + 1 - lo) with (len - 4095) by lia.
    pose proof (Z.div_le_mono (len - 4095) len 4096 ltac:(lia) ltac:(lia)). lia.
  - destruct l' as [|p l'']; [cbn; pose proof (Z.div_pos len 4096 H1 ltac:(lia)); lia|]. exfalso.
    pose proof (proj1 (Forall_forall _ _) F p ltac:(now left)) as X. unfold pg_inside_b in X. cbn [fst snd] in X.
    apply andb_prop in X. destruct X as [X _]. apply andb_prop in X. destruct X as [X1 X2]. apply Z.leb_le in X1. apply Z.leb_le in X2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition vranges_ok (v : vst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(1.(2.=(65.VAL,))(1.(2>.(19.$4.$4.)Lr,(19.$4.$4.)(1.(2.=(3.$4.$4.R1.))(2.=(7.$4.$4.R1.)))(2;.O1.))(2>.(19.$4.$4.)Lr,(19.$4.$4.)(2.=(7.$4.$4.R1.))(2=.O1.))))")
(* [comment removed for export] *).

#[using="Type"] Lemma vgood_card : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.P,(69.R1.)Pl,(61.(30.&40.))P,(36.(30.&40.)R1.)P,(2>.(30.&40.)(4<.R4.)R2.)(2.(62.(63.(30.&40.)R3.))(57.R5.))")
(* [comment removed for export] *).
Proof.
  (intros v dd_H; ddestruct dd_H as (SB & CR & LR); intros l ND F). unfold vnb.
  rewrite (filter_partition_length (fun p => existsb (fun r => pg_shadow_b r p) (csranges v)) l). rewrite Nat2Z.inj_add.
  apply Z.add_le_mono.
  - apply (card_ranges pg_shadow_b npages_shadow (csranges v)).
    + intros r l' Hr ND' F'. pose proof (proj1 (Forall_forall _ _) CR r Hr) as [R0 R1]. apply pg_shadow_card; assumption.
    + apply NoDup_filter. exact ND.
    + apply Forall_forall. intros p Hp. apply filter_In in Hp. exact (proj2 Hp).
  - apply (card_ranges pg_inside_b npages_inside (lazyranges v)).
    + intros r l' Hr ND' F'. pose proof (proj1 (Forall_forall _ _) LR r Hr) as R1. apply pg_inside_card; assumption.
    + apply NoDup_filter. exact ND.
    + apply Forall_forall. intros p Hp. apply filter_In in Hp. destruct Hp as [Hp Hn].
      pose proof (proj1 (Forall_forall _ _) F p Hp) as X. unfold vgood, vgood_b in X.
      apply Bool.orb_true_iff in X. destruct X as [X|X]; [rewrite X in Hn; discriminate| exact X].
Qed.

Definition APOTv (v : vst) (W : vranges_ok v) : apot := APOT (vgood v) (vnb v) (vgood_card v W).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L8890296229.1200000=S1v2mo2EB3BUD". (* [comment removed for export] *)
#[using="Type"] Lemma HKv_ainv : forall v (W : vranges_ok v) mo, HKv v mo -> ainv_std AL (APOTv v W) (vcs v) mo.
Proof.
  (intros v W mo dd_H; ddestruct dd_H as (Hh & ND & GD & LZ & LIM & EB & BUD & _)). split; [exact Hh|]. split; [exact ND|]. split; [exact GD|].
  split; [exact LZ|]. cbn [ap_nb APOTv]. rewrite LIM. unfold page_size. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma HKv_mat_back : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pmo',$6:.P,(6;.R3.R2.)P,(6<.R3.R2.)P,(12.(48.(30.&40.))(49.R3.)(4:.(30.&40.)))P,(36.(30.&40.)(4;.R4.))P,(2>.(30.&40.)(4<.R7.)(4;.R5.))(6;.R8.R6.)")
(* [comment removed for export] *).
Proof.
  intros v mo mo' K MM Hh' ND' GD'.
  ddestruct K as (Hh & ND & GD & LZ & LIM & EB & BUD & WF & TB & CE & RS & RC & VW & AT).
  ddestruct MM as (F1 & F2 & F3 & _).
  unfold HKv. rewrite F2, F3. split; [exact Hh'|]. split; [exact ND'|]. split; [exact GD'|]. split; [exact LZ|].
  split; [exact LIM|]. split; [unfold eager_bytes in *; rewrite F2, F3; exact EB|]. split; [exact BUD|].
  split; [unfold model_ivs_wf in *; rewrite F2, F3; exact WF|].
  split; [exact TB|]. split; [exact CE|]. split; [exact RS|]. split; [exact RC|]. split; [exact VW| exact AT].
Qed.

#[using="Type"] Lemma HKv_top : forall v mo, HKv v mo -> atop_ok (alloc_top (m_vmmaps mo)).
Proof. intros v mo K. exact (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 K))))))))))))). Qed.

#[using="Type"] Theorem HKv_kinv : forall v, vranges_ok v -> kinv AL (vcs v) (HKv v).
Proof.
  intros v W. split.
  - intros mo (Hh & _). exact Hh.
  - intros mo K. exact (HKv_top v mo K).
  - intros mo acc K OK.
    ddestruct (ai_mat (ainv_std_laws AL (APOTv v W)) (vcs v) mo acc (HKv_ainv v W mo K) OK) as (mo' & E & AI' & MM).
    exists mo'. split; [exact E|]. split; [|exact MM].
    ddestruct AI' as (Hh' & ND' & GD' & _). exact (HKv_mat_back v mo mo' K MM Hh' ND' GD').
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L36885742122.49L59308661201.58L59308661201.59L59321181286.5200000;00g01K01eS3hAR1n3N16S3hAR2AL1a1n1x2IN2Rn2Ra1e3CLR1y2Hy3INy2E12E2S3hAR1a1n1x1t1R2IN2Rn2Ra1e3CLM2E12E2S3hAR1v1a1n4STK02CE1x1S2IN". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_apart : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pa,(30.&40.)Pn,(30.&40.)P,(6;.R4.R3.)P,(12.$13.(6=.(1<.(19.(30.&40.)(30.&40.))(5=.(53.R4.))(5:.(53.R4.)))R3.R2.)$15.)P,(2.+10000.(25.&40.R3.))P,(2.(<.(25.&40.R5.)(25.&40.R4.))(37.VhAR,))Px,$4.P,(0.(4>.R9.R1.)(1.(2.(3;.VAL,)R1.)(6.R1.(3<.VAL,))))(9.(1.(2.(25.&40.R8.)R2.)(6.R2.(<.(25.&40.R8.)(25.&40.R7.)))))")
(* [comment removed for export] *).
Proof.
  intros v mo a n K RF N16 CE x Hx IN.
  ddestruct K as (Hh & ND & GD & LZ & LIM & EB & BUD & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & CEN & RS & RC & VW & AT).
  ddestruct VW as (TWF & APT & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & _ & _ & _).
  pose proof (u64_range n) as Rn. pose proof (u64_range a) as Ra.
  pose proof (region_free_clear _ a n ltac:(lia) RF) as CL. apply clear_app_inv in CL. destruct CL as [CLR CLM].
  assert (IMGC : forall y, al_img_lo AL <= y < al_img_hi AL -> ~ (bv_unsigned a <= y < bv_unsigned a + bv_unsigned n)).
  { intros y Hy INy. ddestruct (RC y Hy) as (e & He & E1 & E2). specialize (CLR e He). lia. }
  destruct Hx as [[S|[(I & _ & _)|(t & Ht & CS & R)]]|I].
  - (* [comment removed for export] *) lia.
  - rewrite IMG0, IMG1 in I. exact (IMGC x I IN).
  - pose proof (proj1 (Forall_forall _ _) TB t Ht) as (CV & _). ddestruct CV as (e & He & E1 & E2).
    specialize (CLM e He). unfold t_hi in *. lia.
  - exact (IMGC x I IN).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L11296300927.19L41652814685.19L56941894197.19L57610960851.1900000<00K00X011S3hAR2AL3ILHS3hAR2AL1a1H2H0S3hAR1a1n3N16S3hAR2AL1a1n2A02IL3N162H0". (* [comment removed for export] *)
#[using="Type"] Lemma HKv_fresh_above_img : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pa,(30.&40.)Pn,(30.&40.)P,(6;.R4.R3.)P,(12.$13.(6=.(1<.(19.(30.&40.)(30.&40.))(5=.(53.R4.))(5:.(53.R4.)))R3.R2.)$15.)P,(6.=(25.&40.R4.))P,(2.(3;.VAL,)+10000.)P,(6.(3;.VAL,)(3<.VAL,))P,(2.+10000.(25.&40.R6.))P,(2.(<.(25.&40.R8.)(25.&40.R7.))(37.VhAR,))(2.(3<.VAL,)(25.&40.R9.))")
(* [comment removed for export] *).
Proof.
  intros v mo a n K RF A0 IL ILH N16 CE.
  pose proof (u64_range a) as Ra.
  destruct (Z.le_gt_cases (al_img_hi AL) (bv_unsigned a)) as [H|H]; [exact H|]. exfalso.
  dpose K as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & VW & AT). ddestruct VW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & IMG2 & IMG3 & _ & _ & _ & _).
  destruct (Z.le_gt_cases (al_img_lo AL) (bv_unsigned a)).
  - apply (HKv_apart v mo a n K RF N16 CE (bv_unsigned a)); [right; lia| lia].
  - apply (HKv_apart v mo a n K RF N16 CE (al_img_lo AL)); [right; lia| lia].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L63106954891.5000006S2mo1E". (* [comment removed for export] *)
#[using="Type"] Lemma eager_bytes_sem : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pmo,$6:.P,(58.R1.)(12.$4.(55.R2.)(6>.Lx,$4.(6?.(70.(1<.(19.(30.&40.)(30.&40.))(5;.(53.R3.))(51.R3.))R1.))(5:.(53.R2.))))")
(* [comment removed for export] *).
Proof.
  intros mo WF. pose proof (vm_backing_used_sem mo WF) as E. rewrite vm_backing_used_split in E. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L1947235260.1700000DS1t2lo2hi1e2CL2E12E2". (* [comment removed for export] *)
#[using="Type"] Lemma tracked_apart : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.PM,(61.(19.(30.&40.)(30.&40.)))PN,(61.(19.(30.&40.)(30.&40.)))PLz,(61.(19.(30.&40.)(30.&40.)))Pt,$?.Plo,$4.Phi,$4.P,(59.R7.R6.R5.R4.)P,(10.$?.R4.(11.R8.))P,(71.R8.R4.R3.)P,(6.R5.R4.)(0.(2.R5.(16.R7.))(0.(2.(17.R7.)R6.)(2.(1>.R7.)=)))")
(* [comment removed for export] *).
Proof.
  intros v M N Lz t lo hi (TB & _) Ht CL LH.
  pose proof (proj1 (Forall_forall _ _) TB t Ht) as ((e & He & E1 & E2) & _). specialize (CL e He). unfold t_hi in *. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma vgood_mono : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pv',$68.Pp,(30.&40.)P,Pr,(19.$4.$4.)P,(10.(19.$4.$4.)R1.(2;.R4.))(10.(19.$4.$4.)R2.(2;.R4.))P,Pr,(19.$4.$4.)P,(10.(19.$4.$4.)R1.(2=.R5.))(10.(19.$4.$4.)R2.(2=.R5.))P,(4<.R5.R3.)(4<.R5.R4.)")
(* [comment removed for export] *).
Proof.
  intros v v' p HC HL G. unfold vgood, vgood_b in *. apply Bool.orb_true_iff in G. apply Bool.orb_true_iff.
  destruct G as [G|G]; [left|right]; apply existsb_exists in G; ddestruct G as (r & Hr & X); apply existsb_exists; exists r; split; auto.
Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "00:0?L18926365809.15L18930958230.16L20881291592.10L29430652115.9 L4019985157.11 L47803405442.17L63368234669.11L63368398638.10L63368411926.9 L64792946552.1200000600F00S00Z00g01=01>01?01@01RS2AL1cS2AL2lo1c2S03lenS2lo3len1c2HcS2lo2L0S2lo3len1c2HcS2AL2lo1c2SH2S02M13lenSSSS2AL2lo1c2SH2S02M1". (* [comment removed for export] *)
#[using="Type"] Lemma pg_shadow_hit : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Plo,$4.Plen,$4.Pc,$4.P,(2.=(65.VAL,))P,(2.=R4.)P,(1.(2.R5.R3.)(6.R3.(<.R5.R4.)))P,(6.(24.VAL,R4.)(3?.+2.+40.))(12.$13.(2:.(1:.$4.$4.R7.R6.)(50.(24.VAL,R5.)))$15.)")
(* [comment removed for export] *).
Proof.
  intros lo len c SB L0 Hc SH. unfold pg_shadow_b. cbn [fst snd].
  assert (S0 : 0 <= shadow_of AL lo) by (unfold shadow_of; apply Z.add_nonneg_nonneg; [exact SB| apply Z.div_pos; lia]).
  assert (M1 : shadow_of AL lo <= shadow_of AL c) by (unfold shadow_of; apply Z.add_le_mono_l, Z.div_le_mono; lia).
  assert (M2 : shadow_of AL c <= shadow_of AL (lo + len - 1)) by (unfold shadow_of; apply Z.add_le_mono_l, Z.div_le_mono; lia).
  ddestruct (page_base_of_facts (shadow_of AL c) ltac:(lia)) as (P1 & P2 & P3).
  unfold zpb. apply andb_true_intro. split; [apply andb_true_intro; split; apply Z.leb_le| apply Z.eqb_eq; exact P3].
  - pose proof (Z.div_mod (shadow_of AL lo) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_of AL lo) 4096 ltac:(lia)).
    unfold page_base_of, page_size in *. rewrite u64_lit in * by lia. nia.
  - pose proof (Z.div_mod (shadow_of AL (lo + len - 1)) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_of AL (lo + len - 1)) 4096 ltac:(lia)).
    unfold page_base_of, page_size in *. rewrite u64_lit in * by lia. nia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L36130519557.7L38497188254.7L63842266988.800000700>00IS1x1e1ES1x1e1ES1x1e2E12E2". (* [comment removed for export] *)
#[using="Type"] Lemma ncov_covered : forall N x, ncov N x <-> covered N x = true.
Proof.
  intros N x. unfold ncov, covered. rewrite existsb_exists. split.
  - (intros dd_H; ddestruct dd_H as (e & He & E)). exists e. split; [exact He|]. unfold in_iv, in_rng, B, S. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  - (intros dd_H; ddestruct dd_H as (e & He & E)). exists e. split; [exact He|]. unfold in_iv, in_rng, B, S in E. apply andb_prop in E. destruct E as [E1 E2].
    apply Z.leb_le in E1. apply Z.ltb_lt in E2. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L24928565580.1300000BS2lo2hi1x3OUT1H2H0". (* [comment removed for export] *)
#[using="Type"] Lemma ncov_subtract_keep : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "PN,(61.(19.(30.&40.)(30.&40.)))Plo,$4.Phi,$4.Px,$4.P,(72.R4.)P,(2.R4.R3.)P,(33.R6.R3.)P,(0.(6.R4.R6.)(2.R5.R4.))(33.(73.R8.R7.R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros N lo hi x WF LH NC OUT. apply ncov_covered. ddestruct (maps_subtract_sem N lo hi WF LH) as (_ & _ & CV). rewrite CV.
  apply andb_true_intro. split; [apply ncov_covered; exact NC|]. unfold in_rng.
  destruct (Z.leb_spec lo x); destruct (Z.ltb_spec x hi); cbn; try reflexivity. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L34705151564.18L59308661201.2600000<00]S1H2lo2W12C2S1H2lo2hi1e2CL2LH2C11U1n2UX2E12E2". (* [comment removed for export] *)
#[using="Type"] Lemma hull_fresh_apart : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.PM,(61.(19.(30.&40.)(30.&40.)))PN,(61.(19.(30.&40.)(30.&40.)))PLz,(61.(19.(30.&40.)(30.&40.)))PH,(19.$4.$4.)Plo,$4.Phi,$4.P,(59.R7.R6.R5.R4.)P,(5>.R8.)P,(10.(19.$4.$4.)R5.(35.R9.))P,(71.R9.R5.R4.)P,(6.R6.R5.)(0.(2.R6.(3.$4.$4.R8.))(2.(<.(3.$4.$4.R8.)(7.$4.$4.R8.))R7.))")
(* [comment removed for export] *).
Proof.
  (intros v M N Lz H lo hi dd_H; ddestruct dd_H as (_ & _ & _ & UC & _); intros VW HH CL LH).
  ddestruct VW as (_ & _ & HWF & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HUL & _).
  pose proof (proj1 (Forall_forall _ _) HWF H HH) as (_ & W1 & _).
  destruct (Z.le_gt_cases hi (fst H)) as [C1|C1]; [left; exact C1|].
  destruct (Z.le_gt_cases (fst H + snd H) lo) as [C2|C2]; [right; exact C2|]. exfalso.
  ddestruct (HUL H HH (Z.max lo (fst H)) ltac:(lia)) as (U & n & HU & UX).
  ddestruct (UC U n HU) as (e & He & E1 & E2). specialize (CL e He). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L17220655724.1800000FS1U1n2lo2hi1e2CL2E12E2". (* [comment removed for export] *)
#[using="Type"] Lemma unit_fresh_apart : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.PM,(61.(19.(30.&40.)(30.&40.)))PN,(61.(19.(30.&40.)(30.&40.)))PLz,(61.(19.(30.&40.)(30.&40.)))PU,$4.Pn,$4.Plo,$4.Phi,$4.P,(59.R8.R7.R6.R5.)P,(32.R9.R5.R4.)P,(71.R9.R4.R3.)P,(6.=R6.)(0.(2.(<.R8.R7.)R6.)(2.R5.R8.))")
(* [comment removed for export] *).
Proof.
  (intros v M N Lz U n lo hi dd_H; ddestruct dd_H as (_ & _ & _ & UC & _); intros HU CL N0).
  ddestruct (UC U n HU) as (e & He & E1 & E2). specialize (CL e He). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_add_eager (v : vst) (lo n : Z) (cs : bool) : vst := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(74.(18.$?.(75.O3.O2.$3>.$15.O1.)(11.O4.))(35.O4.)(20.O4.)(5.O4.)(8.O4.)(<.(40.O4.)O2.)(18.(19.$4.$4.)(1:.$4.$4.O3.O2.)(43.O4.))(<.(46.O4.)(<.(64.O2.(3?.+2.+14.))+2.))(<.(47.O4.)(<.(64.O2.(3?.+2.+17.))+2.))(32.O4.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0040>L19172205990.8L41415988076.8L53877237476.8L9690391349.8 00000800900?00ES1S1R2HRSS1R2HRS1S2HS". (* [comment removed for export] *)
#[using="Type"] Lemma rhits_le : forall F S JS R, 0 < S -> 0 <= snd R -> rhits F S JS R <= snd R / S + 2.
Proof. intros F S JS R HS HR. unfold rhits. destruct (_ || _); [| lia]. apply Z.add_nonneg_nonneg; [apply Z.div_pos; lia| lia]. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00`0?L1186817686.83 L13131539002.84L19621671945.84L19864066953.87L2420763460.83 L2425185628.83 L2427330681.82 L2427330681.86 L26696831159.82L2744867246.84 L28783840466.90L29677719528.87L3236455794.84 L32992433899.84L33075001344.87L34184042490.84L34385283113.87L34909900027.89L35710099825.88L36362093169.84L36969038919.89L47878138838.83L50162843968.82L51109213081.75L51111709851.90L51111768481.84L51230418227.83L52439286882.84L52464427497.82L56061752866.83L5744891568.96 L58287161420.90L58354491464.83L59308579027.91L59308972630.99L59310679309.85L59310683405.83L59315137787.76L59338096377.83L61640231099.97L61929658689.69L6277110275.83 L63208222909.85L63374718476.89L63537114425.83L67788525744.82L7009116958.87 L8911144577.85 00000C00O00P00Q00`01701F01U01a02;02R02S02T02n02o03003103@03b04104D04S04_04n05=05L05\06106=06U06k07?07O07f08Y09409N09b0:50:n0;C0;\0<70<C0<D0<P0<Q0<lS3hAR2AL1a1n2ua3IMUS3hAR1a1n2uaFFS3hAR1a1n2ua2N0S3hAR2mo1a1n2ua2N01h2ZLS3hAR1a1n2ua2N0S3hAR1a1n2ua2N0S3hAR1a1n2uaS3hAR1a1n2ua3ACB2Ra2e23CLMS3hAR2AL1a1n3SBH2ua1c1HFFS3hAR1a1n2ua3ACB2Ra2e13CLMFFFS3hAR1a1n2ua2A0S3hAR1a1n2ua3ACB2Ra2e'3CLM1e2T12T2S3hAR1a1n2ua2CES3hAR1a1n2ua2CE1c1RS3hAR1a1n2ua2CES3hAR1a1n2uaS3hAR1a1n2ua2N0S3hAR1a1n2ua2N0S3hAR1a1n2ua2N0S3hAR1a1n2ua3NALS3hAR1v1a1n2ua2N03EB0S3hAR1a1n2uaS3hAR1v1a1n2ua3CE31H3CE4S3hAR1a1n2ua2A02CE1x1RS3hAR1a1n2ua2U92n91HS3hAR1a1n2ua3AL_S3hAR1a1n2ua1H2M22H02M1S3hAR1a1n2ua3ACB2Ra2e'3CLM1x2iv2I12I21R2T12T22P12P2S3hAR1a1n2ua2N03ACB2Ra4APT'S3hAR1a1n2ua2N03ACB2Ra3CLMS3hAR1a1n2ua1t3TL01XS3hAR1a1n2ua3AL_2A0S3hAR1a1n2ua2N02e12X12Y12e22X22Y22e32X32Y33ACB2Ra1H2H02H1S3hAR1a1n2ua2A02CE2N0S3hAR1v2mo1a1n2ua1h2EB2ZLS3hAR1a1n2ua3ACB2Ra2t14APT'S3hAR1a1n2uaFS3hAR1a1n2uaFS3hAR1a1n2ua3ACB2Ra2t24APT'". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_grant_eager : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pa,(30.&40.)Pn,$4.Pcs,$13.P,(6;.R5.R4.)P,(2.=(65.VAL,))P,(6.(65.VAL,)(3?.+2.+3>.))Zua,$4.(25.&40.R6.)P,(12.$4.(27.R1.+1000.)=)P,(6.=R2.)P,(2.(<.R3.R8.)(37.VhAR,))P,(6.=R9.)P,(12.$4.(27.R:.+1000.)=)P,(2.(3<.VAL,)R6.)P,(12.$13.(6=.(1<.(19.(30.&40.)(30.&40.))(5=.(53.R>.))(5:.(53.R>.)))R=.(76.&40.R<.))$15.)P,(2.(<.(<.(40.R10.)R=.)(56.+1000.(57.(77.R10.R8.R=.R<.))))$54.)(6;.(77.R11.R9.R>.R=.)(78.+22.R?.R>.R10.))")
(* [comment removed for export] *).
Proof.
  intros v mo a n cs K SB SBH ua AL_ A0 CE N0 NAL IMU RF BUD.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  dpose VW as (TWF & APT & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  assert (TBL0 : vm_table v (vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo)) (m_vm_lazy mo)) by exact (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))).
  aceilb. 
  pose proof (u64_range a) as Ra. fold ua in Ra.
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  pose proof (region_free_clear _ a (Z_to_bv 64 n) ltac:(rewrite NZ; exact N0) RF) as CL. rewrite NZ in CL. fold ua in CL.
  apply clear_app_inv in CL. destruct CL as [CLR CLM].
  (* [comment removed for export] *)
  assert (APT' : forall t, In t (v_tr v) -> ua + n <= t_lo t \/ t_hi t <= ua).
  { intros t Ht. pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (_ & TL0 & _).
    destruct (tracked_apart v _ _ _ t ua (ua + n) (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))) Ht CLM ltac:(lia)) as [X|[X|X]]; [left; exact X| right; exact X| exfalso; lia]. }
  (* [comment removed for export] *)
  unfold anon_grant. cbv zeta. unfold with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 34)) with false by (vm_compute; reflexivity).
  set (h := m_vmmaps mo). set (mo' := with_vmmaps _ mo).
  assert (PM : m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) by reflexivity.
  assert (PL : m_vm_lazy mo' = m_vm_lazy mo) by reflexivity.
  assert (PT : m_vm_materialized mo' = m_vm_materialized mo) by reflexivity.
  assert (PH : m_halted mo' = m_halted mo) by (subst mo' h; destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity).
  assert (CSR : forall r, In r (csranges v) -> In r (csranges (v_add_eager v ua n cs))).
  { intros r Hr. unfold csranges in *. cbn [v_stk v_img v_tr v_add_eager List.filter map]. cbn in Hr.
    destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr| right; left; exact Hr| right; right].
    apply in_app_iff in Hr. apply in_app_iff. destruct Hr as [Hr|Hr]; [left| right; exact Hr]. destruct cs; [right|]; exact Hr. }
  assert (LZR : forall r, In r (lazyranges v) <-> In r (lazyranges (v_add_eager v ua n cs))).
  { intros r. unfold lazyranges. cbn [v_tr v_add_eager List.filter is_lazy_cs t_kind map]. tauto. }
  assert (WF' : model_ivs_wf mo').
  { ddestruct WF as (W1 & W2 & W3 & W4). unfold model_ivs_wf. rewrite PM, PL. cbn [vm_maps vm_noaccess].
    split; [| split; [exact W2| split; [exact W3| exact W4]]]. apply ivs_wf_cons; [| exact W1]. unfold iv_wf, B, S. cbn [fst snd]. rewrite NZ. fold ua. lia. }
  unfold HKv. rewrite PM, PL, PT, PH. cbn [vm_maps vm_noaccess vm_reserved vm_limit].
  split; [exact Hh|]. split; [exact ND|].
  split. { apply Forall_forall. intros p Hp. apply (vgood_mono v); [exact CSR| intros r Hr; apply (proj1 (LZR r)); exact Hr|].
           exact (proj1 (Forall_forall _ _) GD p Hp). }
  split.
  { (* [comment removed for export] *)
    intros x AOK PIR.
    assert (OLD : aok_addr AL (vcs v) x -> vgood (v_add_eager v ua n cs) (page_base_of x)).
    { intros H. apply (vgood_mono v); [exact CSR| intros r Hr; apply (proj1 (LZR r)); exact Hr|]. exact (LZ x H PIR). }
    assert (NEWCS : forall y, vcs (v_add_eager v ua n cs) y -> vcs v y \/ (cs = true /\ ua <= y < ua + n)).
    { intros y [Y|[Y|(t & Ht & TC & R)]]; [left; left; exact Y| left; right; left; exact Y|].
      destruct Ht as [<-|Ht]; [right; cbn in TC, R; unfold t_hi in R; cbn in R; split; [exact TC| exact R]|].
      left. right. right. exists t. auto. }
    destruct AOK as [CX|[(c & Cc & ->)|IM]].
    - destruct (NEWCS x CX) as [O|[TC R]]; [apply OLD; left; exact O|]. exfalso.
      (* [comment removed for export] *)
      apply page_in_ranges_true in PIR. ddestruct PIR as (iv & Hiv & I1 & I2).
      ddestruct (TL iv Hiv) as (e' & He' & T1 & T2). specialize (CLM e' He').
      ddestruct (page_base_of_facts x ltac:(lia)) as (P1 & P2 & P3). unfold page_size in I2. lia.
    - destruct (NEWCS c Cc) as [O|[TC R]]; [apply OLD; right; left; exists c; auto|].
      unfold vgood, vgood_b. apply Bool.orb_true_iff. left. apply existsb_exists. exists (ua, n). split.
      + unfold csranges. cbn [v_stk v_img v_tr v_ghost v_add_eager List.filter map]. right. right. apply in_app_iff. left. rewrite TC. cbn. left. reflexivity.
      + apply pg_shadow_hit; [exact SB| lia| exact R|]. unfold shadow_of. pose proof (Z.div_le_mono c 0x7fffff800000 8 ltac:(lia) ltac:(lia)). change (0x7fffff800000 / 8) with 17592184995840 in *. lia.
    - apply OLD. right. right. exact IM. }
  split; [exact LIM|].
  split. { (* [comment removed for export] *) rewrite (eager_bytes_sem mo' WF'). rewrite PM, PL. cbn [vm_maps vm_noaccess]. cbn [sum_count v_eb v_add_eager].
           rewrite (eager_bytes_sem mo WF) in EB. fold h in EB.
           pose proof (zcount_le_len (fun x => negb (covered (vm_noaccess h ++ m_vm_lazy mo) x)) (B (a, Z_to_bv 64 n)) (Z.to_nat (S (a, Z_to_bv 64 n)))) as ZL.
           unfold iv_count. unfold S in ZL |- *. cbn [snd] in ZL |- *. rewrite NZ in ZL |- *. rewrite Z2Nat.id in ZL by lia. lia. }
  split; [cbn [v_eb v_add_eager]; exact BUD|].
  split; [exact WF'|].
  split.
  { (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - constructor.
      + (* [comment removed for export] *)
        unfold tfacts, t_hi. cbn [t_lo t_len t_kind t_lit t_cs].
        split; [apply covers_cons_new; rewrite ?NZ; fold ua; lia|].
        split; [intros _; unfold haslit; left; f_equal; subst ua; symmetry; apply Z_to_bv_bv_unsigned|].
        split.
        * intros e He. ddestruct (TN e He) as (e' & He' & T1 & T2). specialize (CLM e' He'). lia.
        * intros e He. ddestruct (TL e He) as (e' & He' & T1 & T2). specialize (CLM e' He'). lia.
      + apply Forall_forall. intros t Ht. pose proof (proj1 (Forall_forall _ _) TB t Ht) as (F1 & F2 & F3).
        split; [apply covers_cons; exact F1|]. split; [intros HL; apply haslit_cons; exact (F2 HL)| exact F3].
    - intros e He. apply covers_cons. exact (TN e He).
    - intros e He. apply covers_cons. exact (TL e He).
    - intros U0 n0 HU0. apply covers_cons. exact (THL U0 n0 HU0).
    - ddestruct TEM as (UNC & MPOS & LZK & MX & MH). split; [| split; [| split; [| split]]].
      + intros U0 n0 HU0 APU x Hx. apply (UNC U0 n0 HU0); [| exact Hx]. intros t Ht. apply APU. right. exact Ht.
      + intros e [<-|He]; [cbn [snd]; rewrite NZ; lia| exact (MPOS e He)].
      + (* [comment removed for export] *)
        intros e He x Hx. destruct (LZK e He x Hx) as [(t & Ht & TLt & Rt)|X]; [left; exists t; split; [right; exact Ht| split; [exact TLt| exact Rt]]| right; exact X].
      + (* [comment removed for export] *)
        intros e [<-|He] x Hx.
        * left. eexists. split; [left; reflexivity|]. split; [reflexivity|]. unfold t_hi. cbn [t_lo t_len]. cbn [fst snd] in Hx. rewrite NZ in Hx. fold ua in Hx. exact Hx.
        * destruct (MX e He x Hx) as [(t & Ht & TLt & Rt)|X]; [left; exists t; split; [right; exact Ht| split; [exact TLt| exact Rt]]| right; exact X].
      + (* [comment removed for export] *)
        intros e H [<-|He] HH M1 M2; [| exact (MH e H He HH M1 M2)]. exfalso. cbn [fst snd] in M1, M2. rewrite NZ in M2. fold ua in M1, M2.
        destruct (hull_fresh_apart v _ _ _ H ua (ua + n) TBL0 VW HH CLM ltac:(lia)); lia.
    - constructor; [| exact MND]. intros Hin. specialize (CLM _ Hin). cbn [fst snd] in CLM. rewrite NZ in CLM. lia.
    - intros e1 e2 [<-|H1] [<-|H2].
      + left. reflexivity.
      + right. specialize (CLM e2 H2). cbn [fst snd]. rewrite NZ. lia.
      + right. specialize (CLM e1 H1). cbn [fst snd]. rewrite NZ. lia.
      + apply MSEP; assumption.
    - exact NZN.
    - exact NZL.
    - ddestruct BANDM as (B1 & B2 & B3). split; [| split]; apply covers_cons; assumption. }
  split.
  { (* [comment removed for export] *)
    split; [| split; [| split]].
    - intros e He R1 R2. apply in_app_iff in He. destruct He as [He|[<-|He]].
      + ddestruct (CE1 e ltac:(apply in_app_iff; left; exact He) R1 R2) as (c & Hc & X). exists c. split; [right; exact Hc| exact X].
      + exists (ua, n). split; [left; reflexivity|]. cbn [fst snd]. rewrite NZ. fold ua. lia.
      + ddestruct (CE1 e ltac:(apply in_app_iff; right; exact He) R1 R2) as (c & Hc & X). exists c. split; [right; exact Hc| exact X].
    - intros c [<-|Hc]; [cbn; lia| apply CE2; exact Hc].
    - cbn [zsum v_cover v_add_eager v_cb20]. pose proof (rhits_le bottomup_floor (2^20) (ACEIL_MIN - bottomup_floor) (ua, n) ltac:(lia) ltac:(cbn; lia)). cbn [snd] in H. lia.  (* [comment removed for export] *)
    - cbn [zsum v_cover v_add_eager v_cb23]. pose proof (rhits_le bottomup_floor (2^23) (ACEIL_MIN - bottomup_floor) (ua, n) ltac:(lia) ltac:(cbn; lia)). cbn [snd] in H. lia. }  (* [comment removed for export] *)
  split; [exact RS|]. split; [exact RC|]. split; [| exact AT].
  (* [comment removed for export] *)
  assert (HAPT : forall H, In H (v_hulls v) -> ua + n <= fst H \/ fst H + snd H <= ua).
  { intros H HH. apply (hull_fresh_apart v _ _ _ H ua (ua + n) (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))) VW HH); [exact CLM| lia]. }
  split.
  { constructor; [| exact TWF]. unfold t_hi. cbn [t_lo t_len t_kind t_cs]. repeat split; try lia; try (intros _; discriminate). }
  split.
  { intros t1 t2 [<-|H1] [<-|H2].
    - left. reflexivity.
    - right. specialize (APT' t2 H2). unfold t_hi in *. cbn [t_lo t_len]. lia.
    - right. specialize (APT' t1 H1). unfold t_hi in *. cbn [t_lo t_len]. lia.
    - apply APT; assumption. }
  split; [exact HWF|]. split; [exact HAP|].
  split.
  { intros t H [<-|Ht] HH; [| apply THA; assumption]. right. unfold t_hi. cbn [t_lo t_len]. apply HAPT. exact HH. }
  assert (BANDNEW : ua + n <= 0x7fff7000 \/ 0x10007fff8000 <= ua).
  { ddestruct BANDM as ((e1 & He1 & X1 & Y1) & (e2 & He2 & X2 & Y2) & (e3 & He3 & X3 & Y3)).
    pose proof (CLM e1 He1). pose proof (CLM e2 He2). pose proof (CLM e3 He3). lia. }
  cbn [v_stk v_img v_eb v_ghost v_tr v_hulls v_unit v_add_eager]. repeat split; try assumption; try lia;
    try (match goal with HU : v_unit v ?U9 ?n9 |- _ => ddestruct (UW U9 n9 HU) as (? & ? & ? & ? & ?); assumption end).
  - intros t [<-|Ht] TC; [unfold t_hi; cbn [t_lo t_len]; exact BANDNEW| apply BANDCS; assumption].
  - constructor; [| exact TND]. intros HIn. specialize (APT' _ HIn). unfold t_hi in APT'. cbn [t_lo t_len] in APT'. lia.
  - (* [comment removed for export] *)
    intros t U9 n9 [<-|Ht] TLt HU9; [| exact (UT t U9 n9 Ht TLt HU9)]. unfold t_hi. cbn [t_lo t_len].
    pose proof (proj1 (UW U9 n9 HU9)) as NP.
    destruct (unit_fresh_apart v _ _ _ U9 n9 ua (ua + n) (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))) HU9 CLM NP); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_add_lazy (v : vst) (lo n : Z) : vst := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(74.(18.$?.(75.O2.O1.$79.$15.$15.)(11.O3.))(35.O3.)(20.O3.)(5.O3.)(8.O3.)(40.O3.)(18.(19.$4.$4.)(1:.$4.$4.O2.O1.)(43.O3.))(<.(46.O3.)(<.(64.O1.(3?.+2.+14.))+2.))(<.(47.O3.)(<.(64.O1.(3?.+2.+17.))+2.))(32.O3.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0150@L1186817686.85  L13131539002.86 L14419301975.84 L18926365809.88 L18926365809.92 L18926563191.93 L18926563318.94 L18933043916.89 L19621671945.86 L19864066953.89 L2420763460.85  L2424962856.86  L2426452985.74  L2427036741.84  L2427036741.88  L26697192587.84 L2706105983.86  L2744867246.86  L28783840466.100L28783840466.90 L29677719528.89 L30389294.86    L3236455794.86  L32992433899.86 L33075001344.89 L34385283113.89 L34909900027.99 L35710099825.90 L36361590730.74 L36368352239.85 L36969038919.99 L39497479604.86 L47878138838.85 L50163336572.84 L51109213081.74 L51111709851.92 L51111768481.86 L51230418227.85 L52463936981.84 L56061752866.85 L57365520411.88 L57365520411.89 L57368009786.94 L5744825905.94  L5744833530.85  L5744962057.88  L5744962057.89  L58287161420.92 L58354491464.85 L59308579027.93 L59310664567.94 L59310679309.87 L59310683405.85 L59315137787.75 L59315300849.97 L59338096377.85 L61640231099.99 L61929658689.68 L62596492723.86 L63208222909.87 L63368150556.89 L63374718476.99 L63537114425.85 L6604881317.84  L67788690572.84 L68390338709.89 L7009116958.89  L8911144577.87  L9846831376.89  00000C00O00[00i01701E01S01a01b01c02202F02U02d03303?03@03Z04304J04K04\04]05705805905J05l06;06J06_07007?07K07Z07i08808H08T08l09N09d0:;0:R0:i0;U0;k0<?0<O0<f0=I0=d0>>0>R0?70?J0@C0@X0A30AN0AZ0Ah0Ai0B50BA0B`0Ba0C<0C[S3hAR2AL1a1n2ua3IMUS3hAR1a1n2uaS3hAR1a1n2uaS3hAR1a1n2ua1xS3hAR1a1n2ua1xS3hAR1a1n2ua1xS3hAR1a1n2ua1xS3hAR1a1n2ua1xFFS3hAR1a1n2ua2N0S3hAR1a1n2ua2N01x2HxS3hAR1a1n2ua2N0S3hAR1a1n2ua2N0S3hAR1a1n2ua2N0S3hAR1a1n2uaFS3hAR1a1n2ua3ACB2Ra2e23CLMS3hAR2AL1a1n3SBH2ua1x1c1HS3hAR2AL1a1n3SBH2ua1c1HFS3hAR1a1n2ua1x2HxFS3hAR1a1n2ua3ACB2Ra2e13CLMFFS3hAR1a1n2ua2A01xS3hAR1a1n2ua3ACB2Ra2e'3CLM1e2T12T2S3hAR1a1n2ua2CES3hAR1a1n2ua2CES3hAR1a1n2ua2CE1x1c1RS3hAR1a1n2ua1x2HxS3hAR1a1n2ua2CES3hAR1a1n2uaS3hAR1a1n2ua2N0S3hAR1a1n2ua2N0S3hAR1a1n2ua2N0S3hAR1a1n2ua3NALS3hAR1a1n2uaS3hAR1v1a1n2ua3CE31H3CE4S3hAR2AL1a1n2ua2CE2N03IMU4IMG21c1YS3hAR1a1n2ua2A02CE1c1RS3hAR1a1n2ua1c1t1R1H2H1S3hAR1a1n2ua1x1t1R1H2H1S3hAR1a1n2ua2A02CE1x2HxS3hAR1v1a1n2ua4STK04STK21x1Y2AL4IMG24IMG42IMS3hAR1a1n2ua2A02CE1x1RS3hAR1a1n2ua2U92n91HS3hAR1a1n2ua3AL_S3hAR1a1n2ua1H2M22H02M1S3hAR1a1n2ua3ACB2Ra1x2Q12Q23AOR3OUTS3hAR1a1n2ua2N03ACB2Ra4APT'S3hAR1a1n2ua2N03ACB2Ra3CLMS3hAR1a1n2ua1t3TL01XS3hAR1a1n2ua3ACB2Ra1x3AOR2P12P23OUT1RS3hAR1a1n2ua3AL_2A0S3hAR1a1n2ua2N02e12X12Y12e22X22Y22e32X32Y33ACB2Ra1H2H02H1S3hAR1a1n2ua2A02CE2N0S3hAR1v2mo1a1n2ua1h2EB4MONOS3hAR1a1n2ua3ACB2Ra2t14APT'S3hAR1a1n2uaS3hAR1a1n2ua1xFS3hAR1a1n2uaS3hAR1a1n2uaS3hAR1v1a1n2ua4STK03ACB2Ra1c2CBFS3hAR1a1n2ua3ACB2Ra2t24APT'S3hAR1v1a1n2ua4STK23ACB2Ra1c2CB". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_grant_lazy : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pa,(30.&40.)Pn,$4.P,(6;.R4.R3.)P,(2.=(65.VAL,))P,(6.(65.VAL,)(3?.+2.+3>.))Zua,$4.(25.&40.R5.)P,(12.$4.(27.R1.+1000.)=)P,(6.=R2.)P,(2.(<.R3.R7.)(37.VhAR,))P,(6.=R8.)P,(12.$4.(27.R9.+1000.)=)P,(2.(3<.VAL,)R6.)P,(12.$13.(6=.(1<.(19.(30.&40.)(30.&40.))(5=.(53.R=.))(5:.(53.R=.)))R<.(76.&40.R;.))$15.)P,(2.(<.(40.R?.)(56.+1000.(57.(7:.R?.R8.R<.))))$54.)(6;.(7:.R10.R9.R=.)(78.+4022.R>.R=.R?.))")
(* [comment removed for export] *).
Proof.
  intros v mo a n K SB SBH ua AL_ A0 CE N0 NAL IMU RF BUD.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  dpose VW as (TWF & APT & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  assert (TBL0 : vm_table v (vm_maps (m_vmmaps mo)) (vm_noaccess (m_vmmaps mo)) (m_vm_lazy mo)) by exact (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))).
  aceilb. 
  pose proof (u64_range a) as Ra. fold ua in Ra.
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  pose proof (region_free_clear _ a (Z_to_bv 64 n) ltac:(rewrite NZ; exact N0) RF) as CL. rewrite NZ in CL. fold ua in CL.
  apply clear_app_inv in CL. destruct CL as [CLR CLM].
  assert (APT' : forall t, In t (v_tr v) -> ua + n <= t_lo t \/ t_hi t <= ua).
  { intros t Ht. pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (_ & TL0 & _).
    destruct (tracked_apart v _ _ _ t ua (ua + n) (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))) Ht CLM ltac:(lia)) as [X|[X|X]]; [left; exact X| right; exact X| exfalso; lia]. }
  (* [comment removed for export] *)
  unfold anon_grant. cbv zeta. unfold with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 16418)) with true by (vm_compute; reflexivity).
  set (h := m_vmmaps mo). set (mo' := vm_add_lazy _ _ (with_vmmaps _ mo)).
  assert (LI : lazy_interior a (Z_to_bv 64 n) = [(a, Z_to_bv 64 n)]).
  { apply lazy_interior_aligned; unfold page_size; rewrite ?NZ; fold ua; [exact AL_| exact NAL| lia| lia]. }
  assert (PM : m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((a, Z_to_bv 64 n) :: vm_maps h) (vm_noaccess h) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) by reflexivity.
  assert (PL : m_vm_lazy mo' = (a, Z_to_bv 64 n) :: m_vm_lazy mo) by (subst mo'; rewrite m_vm_lazy_vm_add_lazy, LI; reflexivity).
  assert (PT : m_vm_materialized mo' = m_vm_materialized mo) by reflexivity.
  assert (PH : m_halted mo' = m_halted mo) by (subst mo' h; destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity).
  assert (CSR : forall r, In r (csranges v) -> In r (csranges (v_add_lazy v ua n))).
  { intros r Hr. unfold csranges in *. cbn [v_stk v_img v_tr v_add_lazy List.filter map]. cbn in Hr.
    destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr| right; left; exact Hr| right; right].
    apply in_app_iff in Hr. apply in_app_iff. destruct Hr as [Hr|Hr]; [left; right; exact Hr| right; exact Hr]. }
  assert (LZR : forall r, In r (lazyranges v) -> In r (lazyranges (v_add_lazy v ua n))).
  { intros r Hr. unfold lazyranges in *. cbn [v_tr v_add_lazy List.filter is_lazy_cs t_kind t_cs map]. right. exact Hr. }
  assert (NEWL : In (ua, n) (lazyranges (v_add_lazy v ua n))).
  { unfold lazyranges. cbn [v_tr v_add_lazy List.filter is_lazy_cs t_kind t_cs map]. left. reflexivity. }
  assert (WF' : model_ivs_wf mo').
  { ddestruct WF as (W1 & W2 & W3 & W4). unfold model_ivs_wf. rewrite PM, PL. cbn [vm_maps vm_noaccess].
    assert (IW : iv_wf (a, Z_to_bv 64 n)) by (unfold iv_wf, B, S; cbn [fst snd]; rewrite NZ; fold ua; lia).
    split; [apply ivs_wf_cons; [exact IW| exact W1]|]. split; [exact W2|]. split; [apply ivs_wf_cons; [exact IW| exact W3]| exact W4]. }
  assert (INS : forall x, ua <= x < ua + n -> pg_inside_b (ua, n) (page_base_of x) = true).
  { intros x Hx. ddestruct (page_base_of_facts x ltac:(lia)) as (P1 & P2 & P3). unfold pg_inside_b. cbn [fst snd].
    apply andb_true_intro. split; [apply andb_true_intro; split; apply Z.leb_le| apply Z.eqb_eq; exact P3].
    - pose proof (Z.div_mod ua 4096 ltac:(lia)). rewrite AL_ in *. pose proof (Z.div_mod (bv_unsigned (page_base_of x)) 4096 ltac:(lia)). rewrite P3 in *. nia.
    - pose proof (Z.div_mod (ua + n) 4096 ltac:(lia)). rewrite Z.add_mod, AL_, NAL in * by lia. cbn in *.
      pose proof (Z.div_mod (bv_unsigned (page_base_of x)) 4096 ltac:(lia)). rewrite P3 in *. nia. }
  unfold HKv. rewrite PM, PL, PT, PH. cbn [vm_maps vm_noaccess vm_reserved vm_limit].
  split; [exact Hh|]. split; [exact ND|].
  split. { apply Forall_forall. intros p Hp. apply (vgood_mono v); [exact CSR| exact LZR|]. exact (proj1 (Forall_forall _ _) GD p Hp). }
  split.
  { intros x AOK PIR.
    destruct (pg_inside_b (ua, n) (page_base_of x)) eqn:PI.
    { unfold vgood, vgood_b. apply Bool.orb_true_iff. right. apply existsb_exists. exists (ua, n). split; [exact NEWL| exact PI]. }
    (* [comment removed for export] *)
    assert (AOR : 0 <= x < 2^64).
    { destruct AOK as [CX|[(c & Cc & ->)|IM]].
      - destruct CX as [Y|[(Y & _ & _)|(t & Ht & TC & R)]]; [cbn [v_stk v_add_lazy] in Y; lia| cbn [v_img v_add_lazy] in Y; rewrite IMG0, IMG1 in Y; lia|]. destruct Ht as [<-|Ht]; [unfold t_hi in R; cbn in R; lia|].
        pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (? & ? & ? & _). unfold t_hi in *. lia.
      - assert (CB : 0 <= c < ACEIL \/ (fst (v_stk v) <= c < snd (v_stk v))).
        { destruct Cc as [Y|[(Y & _ & _)|(t & Ht & TC & R)]]; [right; exact Y| left; cbn [v_img v_add_lazy] in Y; rewrite IMG0, IMG1 in Y; lia|]. destruct Ht as [<-|Ht]; [unfold t_hi in R; cbn in R; left; lia|].
          pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (? & ? & ? & _). unfold t_hi in *. left. lia. }
        unfold shadow_of. split; [apply Z.add_nonneg_nonneg; [exact SB| apply Z.div_pos; lia]|].
        assert (c / 8 <= 2^47 / 8) by (apply Z.div_le_mono; lia). change (2^47/8) with 17592186044416 in *. lia.
      - lia. }
    ddestruct (page_base_of_facts x AOR) as (P1 & P2 & P3).
    assert (OUT : bv_unsigned (page_base_of x) + 4096 <= ua \/ ua + n <= bv_unsigned (page_base_of x)).
    { unfold pg_inside_b in PI. cbn [fst snd] in PI. rewrite (proj2 (Z.eqb_eq _ _) P3), Bool.andb_true_r in PI.
      apply Bool.andb_false_iff in PI.
      pose proof (Z.div_mod ua 4096 ltac:(lia)) as D1. rewrite AL_ in D1.
      pose proof (Z.div_mod n 4096 ltac:(lia)) as D2. rewrite NAL in D2.
      pose proof (Z.div_mod (bv_unsigned (page_base_of x)) 4096 ltac:(lia)) as D3. rewrite P3 in D3.
      destruct PI as [PI|PI]; [apply Z.leb_gt in PI; left| apply Z.leb_gt in PI; right]; nia. }
    rewrite page_in_ranges_cons in PIR. cbn [fst snd] in PIR. rewrite NZ in PIR. fold ua in PIR.
    assert (PIR' : page_in_ranges (page_base_of x) (m_vm_lazy mo) = true).
    { apply Bool.orb_true_iff in PIR. destruct PIR as [PIR|PIR]; [| exact PIR]. exfalso.
      apply andb_prop in PIR. destruct PIR as [Q1 Q2]. apply Z.leb_le in Q1. apply Z.leb_le in Q2. unfold page_size in Q2. lia. }
    assert (OLD : aok_addr AL (vcs v) x -> vgood (v_add_lazy v ua n) (page_base_of x)).
    { intros H. apply (vgood_mono v); [exact CSR| exact LZR|]. exact (LZ x H PIR'). }
    assert (NEWCS : forall y, vcs (v_add_lazy v ua n) y -> vcs v y \/ ua <= y < ua + n).
    { intros y [Y|[Y|(t & Ht & TC & R)]]; [left; left; exact Y| left; right; left; exact Y|].
      destruct Ht as [<-|Ht]; [right; unfold t_hi in R; cbn in R; exact R|]. left. right. right. exists t. auto. }
    destruct AOK as [CX|[(c & Cc & E)|IM]].
    - destruct (NEWCS x CX) as [O|R]; [apply OLD; left; exact O|]. exfalso. lia.
    - destruct (NEWCS c Cc) as [O|R]; [apply OLD; right; left; exists c; auto|].
      unfold vgood, vgood_b. apply Bool.orb_true_iff. left. apply existsb_exists. exists (ua, n). split.
      + unfold csranges. cbn [v_stk v_img v_tr v_ghost v_add_lazy List.filter map t_cs]. right. right. apply in_app_iff. left. left. reflexivity.
      + rewrite E. apply pg_shadow_hit; [exact SB| lia| exact R|]. unfold shadow_of. pose proof (Z.div_le_mono c 0x7fffff800000 8 ltac:(lia) ltac:(lia)). change (0x7fffff800000 / 8) with 17592184995840 in *. lia.
    - apply OLD. right. right. exact IM. }
  split; [exact LIM|].
  split. { (* [comment removed for export] *)
           rewrite (eager_bytes_sem mo' WF'). rewrite PM, PL. cbn [vm_maps vm_noaccess]. cbn [sum_count v_eb v_add_lazy].
           rewrite (eager_bytes_sem mo WF) in EB. fold h in EB.
           assert (Z0 : iv_count (fun x => negb (covered (vm_noaccess h ++ (a, Z_to_bv 64 n) :: m_vm_lazy mo) x)) (a, Z_to_bv 64 n) = 0).
           { unfold iv_count. apply BackingAlgebra.zcount_false. intros x Hx. unfold B, S in Hx. cbn [fst snd] in Hx. rewrite NZ, Z2Nat.id in Hx by lia.
             apply Bool.negb_false_iff. rewrite covered_app. apply Bool.orb_true_iff. right. cbn [covered existsb]. apply Bool.orb_true_iff. left.
             unfold in_iv, in_rng, B, S. cbn [fst snd]. rewrite NZ. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
           rewrite Z0.
           assert (MONO : sum_count (fun x => negb (covered (vm_noaccess h ++ (a, Z_to_bv 64 n) :: m_vm_lazy mo) x)) (vm_maps h)
                          <= sum_count (fun x => negb (covered (vm_noaccess h ++ m_vm_lazy mo) x)) (vm_maps h)).
           { apply sum_count_mono. intros x Hx. apply Bool.negb_true_iff in Hx. apply Bool.negb_true_iff.
             rewrite covered_app in Hx |- *. apply Bool.orb_false_iff in Hx. destruct Hx as [X1 X2]. cbn [covered existsb] in X2.
             apply Bool.orb_false_iff in X2. destruct X2 as [_ X2]. rewrite X1. exact X2. }
           lia. }
  split; [cbn [v_eb v_add_lazy]; exact BUD|].
  split; [exact WF'|].
  split.
  { split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - constructor.
      + unfold tfacts, t_hi. cbn [t_lo t_len t_kind t_lit t_cs].
        split; [apply covers_cons_new; rewrite ?NZ; fold ua; lia|].
        split; [intros _; unfold haslit; left; f_equal; subst ua; symmetry; apply Z_to_bv_bv_unsigned|].
        intros e He. ddestruct (TN e He) as (e' & He' & T1 & T2). specialize (CLM e' He'). lia.
      + apply Forall_forall. intros t Ht. pose proof (proj1 (Forall_forall _ _) TB t Ht) as (F1 & F2 & F3).
        split; [apply covers_cons; exact F1|]. split; [intros HL; apply haslit_cons; exact (F2 HL)|].
        pose proof (APT' t Ht) as AP. pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (_ & TL0 & _).
        destruct (t_kind t); [| exact F3| exact F3].
        destruct F3 as [G1 G2]. split; [exact G1|]. apply clear_cons; [exact G2| rewrite NZ; exact AP].
    - intros e He. apply covers_cons. exact (TN e He).
    - intros e [<-|He].
      + apply covers_cons_new; cbn [fst snd]; lia.
      + apply covers_cons. exact (TL e He).
    - intros U0 n0 HU0. apply covers_cons. exact (THL U0 n0 HU0).
    - ddestruct TEM as (UNC & MPOS & LZK & MX & MH). split; [| split; [| split; [| split]]].
      + intros U0 n0 HU0 APU x Hx. apply (UNC U0 n0 HU0); [| exact Hx]. intros t Ht. apply APU. right. exact Ht.
      + intros e [<-|He]; [cbn [snd]; rewrite NZ; lia| exact (MPOS e He)].
      + (* [comment removed for export] *)
        intros e [<-|He] x Hx.
        * left. eexists. split; [left; reflexivity|]. split; [reflexivity|]. unfold t_hi. cbn [t_lo t_len]. cbn [fst snd] in Hx. rewrite NZ in Hx. fold ua in Hx. exact Hx.
        * destruct (LZK e He x Hx) as [(t & Ht & TLt & Rt)|X]; [left; exists t; split; [right; exact Ht| split; [exact TLt| exact Rt]]| right; exact X].
      + (* [comment removed for export] *)
        intros e [<-|He] x Hx.
        * left. eexists. split; [left; reflexivity|]. split; [reflexivity|]. unfold t_hi. cbn [t_lo t_len]. cbn [fst snd] in Hx. rewrite NZ in Hx. fold ua in Hx. exact Hx.
        * destruct (MX e He x Hx) as [(t & Ht & TLt & Rt)|X]; [left; exists t; split; [right; exact Ht| split; [exact TLt| exact Rt]]| right; exact X].
      + (* [comment removed for export] *)
        intros e H [<-|He] HH M1 M2; [| exact (MH e H He HH M1 M2)]. exfalso. cbn [fst snd] in M1, M2. rewrite NZ in M2. fold ua in M1, M2.
        destruct (hull_fresh_apart v _ _ _ H ua (ua + n) TBL0 VW HH CLM ltac:(lia)); lia.
    - constructor; [| exact MND]. intros Hin. specialize (CLM _ Hin). cbn [fst snd] in CLM. rewrite NZ in CLM. lia.
    - intros e1 e2 [<-|H1] [<-|H2].
      + left. reflexivity.
      + right. specialize (CLM e2 H2). cbn [fst snd]. rewrite NZ. lia.
      + right. specialize (CLM e1 H1). cbn [fst snd]. rewrite NZ. lia.
      + apply MSEP; assumption.
    - exact NZN.
    - intros e [<-|He]; [cbn [snd]; rewrite NZ; exact N0| exact (NZL e He)].
    - ddestruct BANDM as (B1 & B2 & B3). split; [| split]; apply covers_cons; assumption. }
  split.
  { split; [| split; [| split]].
    - intros e He R1 R2. apply in_app_iff in He. destruct He as [He|[<-|He]].
      + ddestruct (CE1 e ltac:(apply in_app_iff; left; exact He) R1 R2) as (c & Hc & X). exists c. split; [right; exact Hc| exact X].
      + exists (ua, n). split; [left; reflexivity|]. cbn [fst snd]. rewrite NZ. fold ua. lia.
      + ddestruct (CE1 e ltac:(apply in_app_iff; right; exact He) R1 R2) as (c & Hc & X). exists c. split; [right; exact Hc| exact X].
    - intros c [<-|Hc]; [cbn; lia| apply CE2; exact Hc].
    - cbn [zsum v_cover v_add_lazy v_cb20]. pose proof (rhits_le bottomup_floor (2^20) (ACEIL_MIN - bottomup_floor) (ua, n) ltac:(lia) ltac:(cbn; lia)). cbn [snd] in H. lia.  (* [comment removed for export] *)
    - cbn [zsum v_cover v_add_lazy v_cb23]. pose proof (rhits_le bottomup_floor (2^23) (ACEIL_MIN - bottomup_floor) (ua, n) ltac:(lia) ltac:(cbn; lia)). cbn [snd] in H. lia. }  (* [comment removed for export] *)
  split; [exact RS|]. split; [exact RC|]. split; [| exact AT].
  assert (HAPT : forall H, In H (v_hulls v) -> ua + n <= fst H \/ fst H + snd H <= ua).
  { intros H HH. apply (hull_fresh_apart v _ _ _ H ua (ua + n) (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))) VW HH); [exact CLM| lia]. }
  split.
  { constructor; [| exact TWF]. unfold t_hi. cbn [t_lo t_len t_kind t_cs]. repeat split; try lia; try (intros _; discriminate). }
  split.
  { intros t1 t2 [<-|H1] [<-|H2].
    - left. reflexivity.
    - right. specialize (APT' t2 H2). unfold t_hi in *. cbn [t_lo t_len]. lia.
    - right. specialize (APT' t1 H1). unfold t_hi in *. cbn [t_lo t_len]. lia.
    - apply APT; assumption. }
  split; [exact HWF|]. split; [exact HAP|].
  split.
  { intros t H [<-|Ht] HH; [| apply THA; assumption]. right. unfold t_hi. cbn [t_lo t_len]. apply HAPT. exact HH. }
  assert (BANDNEW : ua + n <= 0x7fff7000 \/ 0x10007fff8000 <= ua).
  { ddestruct BANDM as ((e1 & He1 & X1 & Y1) & (e2 & He2 & X2 & Y2) & (e3 & He3 & X3 & Y3)).
    pose proof (CLM e1 He1). pose proof (CLM e2 He2). pose proof (CLM e3 He3). lia. }
  cbn [v_stk v_img v_eb v_ghost v_tr v_hulls v_unit v_add_lazy]. repeat split; try assumption; try lia;
    try (match goal with HU : v_unit v ?U9 ?n9 |- _ => ddestruct (UW U9 n9 HU) as (? & ? & ? & ? & ?); assumption end).
  - intros t [<-|Ht] TC; [unfold t_hi; cbn [t_lo t_len]; exact BANDNEW| apply BANDCS; assumption].
  - constructor; [| exact TND]. intros HIn. specialize (APT' _ HIn). unfold t_hi in APT'. cbn [t_lo t_len] in APT'. lia.
  - (* [comment removed for export] *)
    intros t U9 n9 [<-|Ht] TLt HU9; [| exact (UT t U9 n9 Ht TLt HU9)]. unfold t_hi. cbn [t_lo t_len].
    pose proof (proj1 (UW U9 n9 HU9)) as NP.
    destruct (unit_fresh_apart v _ _ _ U9 n9 ua (ua + n) (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM))))))))) HU9 CLM NP); lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition J20 : Z := 89476429.   (* [comment removed for export] *)
Definition J23 : Z := 11184553.   (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00<0?L18926563191.40L26984040175.39L3422768537.38 L35987774815.34L38014092657.39L51313584003.34L56765302024.39L58971515497.39L61259569273.40L62742048647.34L63747082658.38L7100914763.39 00000;00L00Z00m01;01G01e02A02b02m03E03SS1S2JZ2JE1aS1S2JZ2FV2JE1a2A1S1S2JZ2JE1e2R1S1S2JZ2JB2FV3ACV2JES1S2JZ2JE1a2A1S1S2JZ2FV2JES1S2JZ2HS2JB2FV3ACV2JE1a2A12A2S3hAR1S2JZ2JB2FV3ACV2JE1a2A2S1v2mo1S2JZ2HS4EBUD2EB2JE1a2A12A2S1v1S2JZ2JES1S2JZ2JB2FV3ACV2JE1e2R2S1S2JZ2HS2JE1a". (* [comment removed for export] *)
#[using="Type"] Lemma room_gen : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.PS,$4.PJZ,$4.Pflags,$4.P,(6;.R5.R4.)P,(6.=R4.)P,(12.$4.(27.R5.+1000.)=)P,(2.=R5.)P,(2.(<.$41.(56.R6.R7.))$42.)P,(6.(44.(19.$4.$4.)(45.$41.R8.(56.R7.R8.))(43.R:.))R7.)P,P,(12.$4.R7.+22.)(2.(<.(<.(40.R<.)(56.(62.(63.(30.&40.)(4;.R;.)))+1000.))R:.)$54.)(>.(30.&40.)La,(30.&40.)(7;.VhAR,R9.R;.R<.R1.))")
(* [comment removed for export] *).
Proof.
  intros v mo S JZ flags K HS SAL J0 JB SUM EBUD.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & TBL & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  assert (FV : bottomup_floor = 0x2aaaaaaab000) by reflexivity. assert (ACV : ACEIL_MIN = 0x7fff7f800000) by reflexivity.  (* [comment removed for export] *)
  pose proof (Z2Nat.id JZ J0) as JE.
  ddestruct (free_slot_exists_B (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (v_cover v) bottomup_floor S
              (zsum (rhits bottomup_floor S (JZ * S)) (v_cover v)) (Z.to_nat JZ) HS ltac:(lia) ltac:(rewrite JE; lia) CE2) as (a & A1 & A2 & A3 & RF).
  - intros e He R1 R2. unfold ebase, elen in *. rewrite JE in R2. apply CE1; [exact He| lia| lia].
  - rewrite JE. lia.
  - rewrite JE. exact SUM.
  - rewrite JE in A2. exists (Z_to_bv 64 a). unfold anon_grantable. rewrite u64_lit by lia.
    split. { pose proof (Z.div_mod (a - bottomup_floor) S ltac:(lia)) as D1. rewrite A3, Z.add_0_r in D1.
             pose proof (Z.div_mod S 4096 ltac:(lia)) as D2. rewrite SAL, Z.add_0_r in D2.
             set (q := (a - bottomup_floor) / S) in *. set (r := S / 4096) in *.
             replace a with (q * r * 4096 + 11453246123 * 4096) by (rewrite FV in *; nia).
             rewrite <- Z.mul_add_distr_r. apply Z_mod_mult. }
    split; [lia|]. split; [lia|]. split; [lia|]. split; [exact RF|].
    intros HF. rewrite vm_backing_used_split, LIM. specialize (EBUD HF). unfold page_size. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L15043033658.11L15045117696.14L19062989679.14L19172201862.14L23270433927.1400000100900S00[00fSS1S1R2HRS1F1S2JS3JS'1R2HR2LE2H12H2S1S1R2HRS1S1R2HR2H0". (* [comment removed for export] *)
#[using="Type"] Lemma rhits_mono : forall F S JS JS' R, 0 < S -> 0 <= snd R -> JS <= JS' -> rhits F S JS R <= rhits F S JS' R.
Proof.
  intros F S JS JS' R HS HR LE. unfold rhits.
  destruct (Z.leb_spec (fst R + snd R) F); cbn [orb]; [lia|].
  pose proof (Z.div_pos (snd R) S HR HS).
  destruct (Z.leb_spec (F + JS) (fst R)); destruct (Z.leb_spec (F + JS') (fst R)); cbn; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L15045197237.9 L50704596484.1300000100FSS1F1S2JS3JS'1R1r2IH1H". (* [comment removed for export] *)
#[using="Type"] Lemma zsum_rhits_mono : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "PF,$4.PS,$4.PJS,$4.PJS',$4.Pl,(61.(19.$4.$4.))P,(6.=R4.)P,PR,(19.$4.$4.)P,(10.(19.$4.$4.)R1.R3.)(2.=(7.$4.$4.R2.))P,(2.R5.R4.)(2.(44.(19.$4.$4.)(45.R8.R7.R6.)R4.)(44.(19.$4.$4.)(45.R8.R7.R5.)R4.))")
(* [comment removed for export] *).
Proof.
  intros F S JS JS' l HS HR LE. induction l as [|R r IH]; cbn; [lia|].
  pose proof (rhits_mono F S JS JS' R HS (HR R ltac:(now left)) LE). specialize (IH ltac:(intros; apply HR; now right)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma HKv_mat_le : forall v mo, vranges_ok v -> HKv v mo -> Z.of_nat (length (m_vm_materialized mo)) <= vnb v.
Proof. (intros v mo W dd_H; ddestruct dd_H as (Hh & ND & GD & _)). apply (vgood_card v W); assumption. Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L16448997332.28L23745279192.28L35585344741.30L58712206489.28L67788820751.2800000100200?00@00ASSS1v2mo4EBUD1HSS". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_room20 : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pflags,$4.P,(69.R3.)P,(6;.R4.R3.)P,(6.(46.R5.)$7<.)P,P,(12.$4.R4.+22.)(2.(<.(<.(40.R7.)(56.+1000.(57.R7.)))(3?.+2.+14.))$54.)(>.(30.&40.)La,(30.&40.)(7;.VhAR,R6.(3?.+2.+14.)R7.R1.))")
(* [comment removed for export] *).
Proof.
  intros v mo flags W K CB EBUD.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & TBL & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  assert (FV : bottomup_floor = 0x2aaaaaaab000) by reflexivity. assert (ACV : ACEIL_MIN = 0x7fff7f800000) by reflexivity.  (* [comment removed for export] *)
  apply (room_gen v mo (2^20) J20 flags K); [lia| reflexivity| unfold J20; lia| rewrite FV, ACV; unfold J20; lia| |].
  - eapply Z.le_lt_trans; [| exact CB]. eapply Z.le_trans; [| exact CE3]. apply zsum_rhits_mono; [lia| exact CE2| rewrite FV, ACV; unfold J20; lia].
  - intros HF. specialize (EBUD HF). pose proof (HKv_mat_le v mo W K). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L17745709641.28L24197634836.28L38931255765.30L43992945816.28L50163204351.2800000100200?00@00ASSS1v2mo4EBUD1HSS". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_room23 : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pflags,$4.P,(69.R3.)P,(6;.R4.R3.)P,(6.(47.R5.)$7=.)P,P,(12.$4.R4.+22.)(2.(<.(<.(40.R7.)(56.+1000.(57.R7.)))(3?.+2.+17.))$54.)(>.(30.&40.)La,(30.&40.)(7;.VhAR,R6.(3?.+2.+17.)R7.R1.))")
(* [comment removed for export] *).
Proof.
  intros v mo flags W K CB EBUD.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & TBL & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  assert (FV : bottomup_floor = 0x2aaaaaaab000) by reflexivity. assert (ACV : ACEIL_MIN = 0x7fff7f800000) by reflexivity.  (* [comment removed for export] *)
  apply (room_gen v mo (2^23) J23 flags K); [lia| reflexivity| unfold J23; lia| rewrite FV, ACV; unfold J23; lia| |].
  - eapply Z.le_lt_trans; [| exact CB]. eapply Z.le_trans; [| exact CE4]. apply zsum_rhits_mono; [lia| exact CE2| rewrite FV, ACV; unfold J23; lia].
  - intros HF. specialize (EBUD HF). pose proof (HKv_mat_le v mo W K). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition v_add_sub (v : vst) (lo n : Z) (cs : bool) : vst := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(74.(18.$?.(75.O3.O2.$3>.$3=.O1.)(11.O4.))(35.O4.)(20.O4.)(5.O4.)(8.O4.)(<.(40.O4.)O2.)(43.O4.)(46.O4.)(47.O4.)(32.O4.))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010>L66646037945.9000001S". (* [comment removed for export] *)
#[using="Type"] Lemma overlap_sum_le_len : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pl,(61.(19.(30.&40.)(30.&40.)))Plo,$4.Phi,$4.P,(2.R2.R1.)P,Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.R5.)(0.(2.(<.(25.&40.(3.(30.&40.)(30.&40.)R2.))(25.&40.(7.(30.&40.)(30.&40.)R2.)))R5.)(2.R4.(25.&40.(3.(30.&40.)(30.&40.)R2.))))(12.$4.(7>.R5.R4.R3.)=)")
(* [comment removed for export] *).
Proof.
  intros l lo hi LH H. induction l as [|e r IH]; [reflexivity|]. rewrite overlap_sum_cons, IH by (intros; apply H; now right).
  rewrite (iv_count_in_rng_disjoint e lo hi); [lia|]. unfold B, S. apply H. now left.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0050?L13053786433.29L13060064633.30L13068484316.28L43865506301.31L44894536659.3100000800@00H00^011S1U1n2N0S1U1n2N0S1U1n2N0S1U1n2e02l12l21H2H02H1S1U1n2e02E12E21e2AP". (* [comment removed for export] *)
#[using="Type"] Lemma overlap_sum_sub : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.PM,(61.(19.(30.&40.)(30.&40.)))PN,(61.(19.(30.&40.)(30.&40.)))PLz,(61.(19.(30.&40.)(30.&40.)))PU,$4.Pn,$4.P,(59.R6.R5.R4.R3.)P,(31.R6.R3.(<.R3.R2.))P,(6.=R3.)(2.(7>.R8.R5.(<.R5.R4.))R4.)")
(* [comment removed for export] *).
Proof.
  (intros v M N Lz U n dd_H; ddestruct dd_H as (TB & TN & TL & UC & UNP & MND & MSEP & NZN & NZL & BANDM); intros dd_H; ddestruct dd_H as (e0 & He0 & E1 & E2); intros N0).
  pose proof He0 as He0M. apply in_split in He0. ddestruct He0 as (l1 & l2 & EM).
  assert (ND' := MND). rewrite EM in ND'. apply NoDup_remove in ND'. destruct ND' as [_ NIN].
  rewrite EM. rewrite overlap_sum_app, overlap_sum_cons.
  assert (OTHERS : forall e, In e (l1 ++ l2) -> eB e + eS e <= U \/ U + n <= eB e).
  { intros e He.
    assert (HeM : In e M) by (rewrite EM; apply in_app_iff in He; apply in_app_iff; destruct He; [left| right; right]; assumption).
    destruct (MSEP e e0 HeM He0M) as [<-|AP]; [exfalso; exact (NIN He)| lia]. }
  pose proof (overlap_sum_le_len l1 U (U + n) ltac:(lia) ltac:(intros; apply OTHERS; apply in_app_iff; now left)).
  pose proof (overlap_sum_le_len l2 U (U + n) ltac:(lia) ltac:(intros; apply OTHERS; apply in_app_iff; now right)).
  pose proof (iv_count_in_rng_le e0 U (U + n) ltac:(lia)). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "01?0@L10072007836.98 L13058043995.97 L13060071729.107L13060471105.94 L14702413436.98 L17300083895.106L17302376639.81 L17302396704.82 L18344525933.98 L1868273648.100 L18926661658.22 L18926759668.92 L18926759668.93 L18926759926.95 L18928778642.97 L18928845357.93 L18928845357.94 L19613186818.97 L19859804819.97 L20628780141.97 L21303640324.79 L23144198646.88 L2424860234.81  L2424873429.82  L2424874332.97  L2426990146.97  L2427412546.83  L2427412578.98  L24816150141.94 L25964171064.93 L25964302265.89 L26888031189.91 L28785946858.107L28853280204.104L30493818137.93 L31332368219.112L3228297849.97  L33070870810.97 L34391585809.100L36969038919.106L38102416844.97 L39147365310.96 L39822995928.100L4137553233.99  L41982941717.104L44827158554.91 L44838168560.98 L44838246860.97 L44894663280.86 L46957476335.99 L47425004964.97 L47484416664.97 L49685448931.100L51133698258.97 L51228385333.97 L51644625213.99 L52427764692.91 L52431129449.97 L52553944276.108L56606873788.98 L59308972630.115L59310679309.98 L59310860012.102L59377646407.23 L60095729573.81 L60095774778.82 L61929571768.80 L63368429084.91 L63368447790.92 L63374718476.106L63551727679.97 L63842446571.110L64192629537.100L66086610871.92 L66212408630.107L66622374278.88 L66938867636.97 L68044391805.93 L7007018790.100 00000A00O00]00k01901K01]01o02G02H02M02\02k03:03H03W03f03g04904:04U04n05<05J05[05i06706E06`07E07b08208I08[09009M09N09]09^0:30:D0:b0;<0;R0;d0<40<G0<W0=50=Y0=d0>=0>>0>I0>X0>n0?@0?T0@10@?0@d0A:0AX0A]0An0B?0BZ0Bi0C80CC0CD0C^0C_0D10DO0Dh0EE0E[0E\S3hAR2mo1H1U1n2H0S3hAR1H1U1n2N0S3hAR1H1U1n2N0S3hAR1H1U1n2N0S3hAR1H1U1n2U0S3hAR1H1U1n2U03H68S3hAR1H1U1n2U03H68S3hAR1H1U1n2U03H68S3hAR1H1U1n2U02U12W53ACBFS1U1nS3hAR1H1U1n1p1rS3hAR1H1U1n1p1rS3hAR1H1U1n1p1rS3hAR2mo1H1U1nS3hAR1H1U1n1p1rS3hAR1H1U1n1p1rFS3hAR1H1U1n2U03H68FS3hAR1H1U1n2U02U12N03H682W2S3hAR2AL1H1U1n3IMH4IMG21pS3hAR1H1U1n2N0S3hAR1H1U1n2N0S3hAR2mo1H1U1n2N0S3hAR1H1U1n2N0S3hAR1H1U1n2N0S3hAR1H1U1n2N0S3hAR1H1U1n1p1r2X12H02H12H2S3hAR1H1U1n2U02U12W53ACB1p1r2RB2P02P1S3hAR1H1U1n1t3APT3ACB1p2X12X2S3hAR1H1U1n1p2H0S3hAR2AL1H1U1n3ASB1c2H0S3hAR1H1U1n1e1r2R1S3hAR1H1U1n1p1r2H02H2S3hAR1H1U1n2U02U13H682W21y2HyFS3hAR1H1U1n3UALFS3hAR1H1U1n2U12W21c1RS3hAR1H1U1n2U12W2S3hAR1H1U1n1p1r2X22H02H12H22H3S3hAR1H1U1n2U02U13ACB2H'1XS3hAR1H1U1n2t23APT3ACBS3hAR1H1U1n1e1r2R2S3hAR1H1U1n1p2H0S3hAR1v2mo1H1U1n2H0S3hAR1v2mo1H1U1nS3hAR2AL1H1U1n3IMH2U03H681e2H1S3hAR1v2mo1H1U1n2cs3BUD2EB2OV2ML3VNBS3hAR1H1U1nS3hAR2AL1H1U1n3IMH2U03H68FS3hAR1H1U1nS3hAR1H1U1n3NALS3hAR1H1U1n2t13APT3ACBS3hAR1H1U1n1p1r2RBS3hAR1v1H1U1n2N03EB0S3hAR1H1U1n1x1q2Q12Q21r2R12R2S3hAR1H1U1n2U1S3hAR1H1U1n3ACB1y2Hy1q2Q12Q22R32P12P2S3hAR1H1U1n2N03APT3ACBS3hAR1H1U1n2N01e2E12E23ACB3CLMS1U1nS3hAR1H1U1n2U12W2S3hAR1H1U1n2U12W2S3hAR1H1U1n2U02U12N03H682W2S3hAR1H1U1n1p1rS3hAR1H1U1n1p1rS3hAR1H1U1nFS3hAR1H1U1n1e1x2Hx1r2R12R2FS3hAR1H1U1n1p1r2RBS3hAR1H1U1n3ACB2U92n93APU1x2HxS3hAR1v1H1U1n4STK04STK21pS3hAR1v2mo1H1U1n2EB2OV3mo'2BFS3hAR1H1U1n1p2t02H02H2F". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_commit_sub : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.PH,(19.$4.$4.)PU,$4.Pn,$4.Pcs,$13.P,(69.R6.)P,(6;.R7.R6.)P,(12.$4.(65.VAL,)+7???8000.)P,(2.(3<.VAL,)+65?000.)P,(10.(19.$4.$4.)R8.(35.R:.))P,(2.(3.$4.$4.R9.)R8.)P,(2.(<.R9.R8.)(<.(3.$4.$4.R:.)(7.$4.$4.R:.)))P,(12.$4.(27.R:.+1000.)=)P,(12.$4.(27.R:.+1000.)=)P,(6.=R;.)P,(2.+65?000.(3.$4.$4.R>.))P,(32.R11.R>.R=.)P,Pt,$?.P,(10.$?.R1.(11.R13.))(0.(2.(<.R11.R10.)(16.R2.))(2.(17.R2.)R11.))P,(2.(<.(<.(40.R13.)R?.)(56.+1000.(57.(7?.R13.R10.R?.R>.))))$54.)(1.(6;.(7?.R14.R11.R10.R?.)(80.+32.R11.R10.R13.))(1.(12.$13.(81.(5:.(53.R13.))(76.&40.R11.)(76.&40.R10.))$15.)(1.(12.$13.(6=.(5=.(53.R13.))(76.&40.R11.)(76.&40.R10.))$15.)(82.+32.R11.R10.R13.))))")
(* [comment removed for export] *).
Proof.
  intros v mo H U n cs VR K ASB IMH HH U0 U1 UAL NAL N0 H68 HUN APT BUD.
  assert (SB : 0 <= al_sb AL) by (rewrite ASB; lia). assert (SBH : al_sb AL < 2^62) by (rewrite ASB; lia).
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  pose proof (THL U n HUN) as HL.   (* [comment removed for export] *)
  pose proof (proj1 (Forall_forall _ _) HWF H HH) as (W0 & W1 & W2 & W3 & W4 & W5).
  aceilb. 
  assert (UZ : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  (* [comment removed for export] *)
  assert (MC : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 U) (Z_to_bv 64 n) = true).
  { apply covers_map_contains; [lia| lia| lia| exact HL]. }
  assert (RFR : region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 U) (Z_to_bv 64 n) = true).
  { apply clear_region_free; [lia| lia| lia|]. intros e He. destruct (RS e He). lia. }
  assert (OV : overlap_sum (vm_maps (m_vmmaps mo)) U (U + n) <= n).
  { eapply (overlap_sum_sub v _ _ _ U n); [exact (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM)))))))))| exact HL| lia]. }
  (* [comment removed for export] *)
  assert (MATOUT : forall p, vgood v p -> bv_unsigned p + 4096 <= U \/ U + n <= bv_unsigned p).
  { intros p G. unfold vgood, vgood_b in G. apply Bool.orb_true_iff in G. destruct G as [G|G]; apply existsb_exists in G; ddestruct G as (r & Hr & X).
    - (* [comment removed for export] *)
      unfold pg_shadow_b in X. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
      apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.eqb_eq in X3.
      assert (RB : 0 <= fst r /\ fst r + snd r <= 2^47).
      { unfold csranges in Hr. cbn in Hr. destruct Hr as [<-|[<-|Hr]]; cbn [fst snd].
        - lia. - rewrite IMG0, IMG1. lia.
        - apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
          + apply in_map_iff in Hr. ddestruct Hr as (t0 & <- & Ht0). apply filter_In in Ht0. destruct Ht0 as [Ht0 _].
            pose proof (proj1 (Forall_forall _ _) TWF t0 Ht0) as (? & ? & ? & _). cbn [fst snd]. unfold t_hi in *. lia.
          + pose proof (proj1 (Forall_forall _ _) GWF r Hr) as (? & ? & ?). lia. }
      unfold zpb, shadow_of in X1, X2. rewrite ASB in X1, X2.
      assert (P0 : 0x7fff8000 <= bv_unsigned p).
      { pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_mod (2147450880 + fst r / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + fst r / 8) 4096 ltac:(lia)). lia. }
      assert (P1 : bv_unsigned p + 4096 <= 0x10007fff8000).
      { assert ((fst r + snd r - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
        pose proof (Z.div_mod (2147450880 + (fst r + snd r - 1) / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + (fst r + snd r - 1) / 8) 4096 ltac:(lia)).
        pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). rewrite X3 in *. lia. }
      lia.
    - (* [comment removed for export] *)
      unfold lazyranges in Hr. apply in_map_iff in Hr. ddestruct Hr as (t & <- & Ht). apply filter_In in Ht. destruct Ht as [Ht _].
      unfold pg_inside_b in X. cbn [fst snd] in X. apply andb_prop in X. destruct X as [X _]. apply andb_prop in X. destruct X as [X1 X2].
      apply Z.leb_le in X1. apply Z.leb_le in X2. specialize (APT t Ht). unfold t_hi in APT. lia. }
  (* [comment removed for export] *)
  unfold fixrw_commit. cbv zeta. unfold with_mmap_replacement, with_mmap_backing.
  replace (mmap_noreserve_b (Z_to_bv 64 50)) with false by (vm_compute; reflexivity).
  rewrite UZ, NZ. set (h := m_vmmaps mo). set (mo' := vm_forget_range _ _ _).
  assert (PM : m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) (maps_subtract (vm_noaccess h) U (U + n)) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)).
  { subst mo'. rewrite m_vmmaps_vm_forget_range. unfold mmap_fixed_rw_next. rewrite UZ, NZ. reflexivity. }
  assert (PL : m_vm_lazy mo' = maps_subtract (m_vm_lazy mo) U (U + n)) by (subst mo'; rewrite m_vm_lazy_vm_forget_range; reflexivity).
  assert (PT : m_vm_materialized mo' = m_vm_materialized mo).
  { subst mo'. rewrite m_vm_materialized_vm_forget_range, m_vm_materialized_with_vmmaps.
    rewrite forallb_filter_id; [reflexivity|]. apply forallb_forall. intros p Hp.
    pose proof (MATOUT p (proj1 (Forall_forall _ _) GD p Hp)) as X. unfold page_outside_range.
    apply Bool.negb_true_iff. apply Bool.andb_false_iff. destruct X; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; lia. }
  assert (PH : m_halted mo' = m_halted mo) by (subst mo' h; destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity).
  ddestruct WF as (W1' & W2' & W3' & W4').
  assert (WF' : model_ivs_wf mo').
  { unfold model_ivs_wf. rewrite PM, PL. cbn [vm_maps vm_noaccess]. split; [exact W1'|]. split; [| split; [| exact W4']]; apply maps_subtract_wf; try assumption; lia. }
  assert (CSR : forall r, In r (csranges v) -> In r (csranges (v_add_sub v U n cs))).
  { intros r Hr. unfold csranges in *. cbn [v_stk v_img v_tr v_add_sub List.filter map]. cbn in Hr.
    destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr| right; left; exact Hr| right; right].
    apply in_app_iff in Hr. apply in_app_iff. destruct Hr as [Hr|Hr]; [left| right; exact Hr]. destruct cs; [right|]; exact Hr. }
  assert (LZR : forall r, In r (lazyranges v) <-> In r (lazyranges (v_add_sub v U n cs))).
  { intros r. unfold lazyranges. cbn [v_tr v_add_sub List.filter is_lazy_cs t_kind map]. tauto. }
  split; [| split; [exact MC| split; [exact RFR|]]].
  2:{ (* [comment removed for export] *)
      split.
      - intros _. apply mmap_fixed_rw_budget_ok_commit_intro; [vm_compute; reflexivity| exact (conj W1' (conj W2' (conj W3' W4')))|].
        rewrite UZ, NZ, vm_backing_used_split, LIM.
        pose proof (HKv_mat_le v mo VR K) as ML.
        assert (VNB : vnb v <= vnb (v_add_sub v U n cs)).
        { unfold vnb, csranges, lazyranges. cbn [v_stk v_img v_tr v_ghost v_add_sub List.filter t_cs is_lazy_cs t_kind map zsum].
          destruct cs; cbn [map zsum app]; [| lia]. cbn [t_lo t_len].
          assert (0 <= npages_shadow (U, n)) by (unfold npages_shadow; cbn [snd]; pose proof (Z.div_pos n 32768 ltac:(lia) ltac:(lia)); lia). lia. }
        unfold page_size. lia.
      - intros RF2 _. exfalso. pose proof (region_free_clear _ (Z_to_bv 64 U) (Z_to_bv 64 n) ltac:(rewrite NZ; lia) RF2) as CL.
        rewrite UZ, NZ in CL. apply clear_app_inv in CL. destruct CL as [_ CLM].
        ddestruct HL as (e & He & E1 & E2). specialize (CLM e He). lia. }
  unfold HKv. rewrite PM, PL, PT, PH. cbn [vm_maps vm_noaccess vm_reserved vm_limit].
  split; [exact Hh|]. split; [exact ND|].
  split. { apply Forall_forall. intros p Hp. apply (vgood_mono v); [exact CSR| intros r Hr; apply (proj1 (LZR r)); exact Hr|].
           exact (proj1 (Forall_forall _ _) GD p Hp). }
  split.
  { (* [comment removed for export] *)
    intros x AOK PIR.
    assert (PIR0 : page_in_ranges (page_base_of x) (m_vm_lazy mo) = true).
    { apply page_in_ranges_true in PIR. ddestruct PIR as (q & Hq & Q1 & Q2).
      destruct (maps_subtract_pieces _ _ _ q W3' Hq) as (r & Hr & R1 & R2 & R3).
      apply (proj2 (page_in_ranges_true _ _)). exists r. split; [exact Hr| lia]. }
    assert (NOTIN : forall y, U <= y < U + n -> page_in_ranges (page_base_of y) (maps_subtract (m_vm_lazy mo) U (U + n)) = true -> False).
    { intros y Hy P. apply page_in_ranges_true in P. ddestruct P as (q & Hq & Q1 & Q2).
      destruct (maps_subtract_pieces _ _ _ q W3' Hq) as (r & Hr & R1 & R2 & R3).
      ddestruct (page_base_of_facts y ltac:(lia)) as (P1 & P2 & P3). unfold page_size in Q2. lia. }
    assert (OLD : aok_addr AL (vcs v) x -> vgood (v_add_sub v U n cs) (page_base_of x)).
    { intros Ha. apply (vgood_mono v); [exact CSR| intros r Hr; apply (proj1 (LZR r)); exact Hr|]. exact (LZ x Ha PIR0). }
    assert (NEWCS : forall y, vcs (v_add_sub v U n cs) y -> vcs v y \/ (cs = true /\ U <= y < U + n)).
    { intros y [Y|[Y|(t & Ht & TC & R)]]; [left; left; exact Y| left; right; left; exact Y|].
      destruct Ht as [<-|Ht]; [right; cbn in TC, R; unfold t_hi in R; cbn in R; split; [exact TC| exact R]|].
      left. right. right. exists t. auto. }
    destruct AOK as [CX|[(c & Cc & ->)|IM]].
    - destruct (NEWCS x CX) as [O|[TC R]]; [apply OLD; left; exact O|]. exfalso. exact (NOTIN x R PIR).
    - destruct (NEWCS c Cc) as [O|[TC R]]; [apply OLD; right; left; exists c; auto|].
      unfold vgood, vgood_b. apply Bool.orb_true_iff. left. apply existsb_exists. exists (U, n). split.
      + unfold csranges. cbn [v_stk v_img v_tr v_ghost v_add_sub List.filter map]. right. right. apply in_app_iff. left. rewrite TC. cbn. left. reflexivity.
      + apply pg_shadow_hit; [exact SB| lia| exact R|]. unfold shadow_of. pose proof (Z.div_le_mono c 0x7fffff800000 8 ltac:(lia) ltac:(lia)). change (0x7fffff800000 / 8) with 17592184995840 in *. lia.
    - apply OLD. right. right. exact IM. }
  split; [exact LIM|].
  split. { (* [comment removed for export] *)
           pose proof (backing_forget_commit_le mo (mmap_fixed_rw_next h (Z_to_bv 64 U) (Z_to_bv 64 n))
                         U (U + n) (conj W1' (conj W2' (conj W3' W4'))) ltac:(lia) eq_refl ltac:(unfold mmap_fixed_rw_next; cbn [vm_noaccess]; rewrite UZ, NZ; reflexivity)) as BF.
           change (vm_forget_range U (U + n) (with_vmmaps (mmap_fixed_rw_next h (Z_to_bv 64 U) (Z_to_bv 64 n)) mo)) with mo' in BF.
           rewrite !vm_backing_used_split, PT in BF. cbn [v_eb v_add_sub]. subst h. lia. }
  split; [cbn [v_eb v_add_sub]; exact BUD|].
  split; [exact WF'|].
  split.
  { (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - constructor.
      + unfold tfacts, t_hi. cbn [t_lo t_len t_kind t_lit t_cs].
        split. { exact HL. }
        split; [intros X; discriminate|].
        split; [apply clear_subtract_cut; [exact W2'| lia| lia] | apply clear_subtract_cut; [exact W3'| lia| lia]].
      + apply Forall_forall. intros t Ht. pose proof (proj1 (Forall_forall _ _) TB t Ht) as (F1 & F2 & F3).
        pose proof (APT t Ht) as AP. pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (_ & TL0 & _).
        split; [exact F1|]. split; [exact F2|].
        destruct (t_kind t).
        * destruct F3 as [G1 G2]. split; apply clear_subtract; assumption.
        * apply clear_subtract; assumption.
        * exact I.
    - intros e He. destruct (maps_subtract_pieces _ _ _ e W2' He) as (r & Hr & R1 & R2 & R3).
      eapply covers_weaken; [exact (TN r Hr)| lia| lia].
    - intros e He. destruct (maps_subtract_pieces _ _ _ e W3' He) as (r & Hr & R1 & R2 & R3).
      eapply covers_weaken; [exact (TL r Hr)| lia| lia].
    - exact THL.
    - ddestruct TEM as (UNC & MPOS & LZK & MX & MH). split; [| split; [exact MPOS| split; [| split; [| exact MH]]]].
      { (* [comment removed for export] *)
        intros U9 n9 HU9 APU x Hx. apply ncov_subtract_keep; [exact W2'| lia| | ].
        + apply (UNC U9 n9 HU9); [| exact Hx]. intros t Ht. apply APU. right. exact Ht.
        + specialize (APU (TR U n KEager false cs) ltac:(left; reflexivity)). unfold t_hi in APU. cbn [t_lo t_len] in APU. lia. }
      { (* [comment removed for export] *)
        intros e He x Hx. destruct (maps_subtract_pieces _ _ _ e W3' He) as (r & Hr & R1 & R2 & R3).
        destruct (LZK r Hr x ltac:(lia)) as [(t & Ht & TLt & Rt)|X]; [left; exists t; split; [right; exact Ht| split; [exact TLt| exact Rt]]| right; exact X]. }
      (* [comment removed for export] *)
      intros e He x Hx. destruct (MX e He x Hx) as [(t & Ht & TLt & Rt)|X]; [left; exists t; split; [right; exact Ht| split; [exact TLt| exact Rt]]| right; exact X].
    - exact MND.
    - exact MSEP.
    - intros e He. eapply maps_subtract_pos; [exact W2'| exact NZN| exact He].
    - intros e He. eapply maps_subtract_pos; [exact W3'| exact NZL| exact He].
    - exact BANDM. }
  split; [exact (conj CE1 (conj CE2 (conj CE3 CE4)))|].
  split; [exact RS|]. split; [exact RC|]. split; [| exact AT].
  (* [comment removed for export] *)
  split.
  { constructor; [| exact TWF]. unfold t_hi. cbn [t_lo t_len t_kind t_cs]. repeat split; try lia; try (intros _; discriminate). }
  split.
  { intros t1 t2 [<-|H1] [<-|H2].
    - left. reflexivity.
    - right. specialize (APT t2 H2). unfold t_hi in *. cbn [t_lo t_len]. lia.
    - right. specialize (APT t1 H1). unfold t_hi in *. cbn [t_lo t_len]. lia.
    - apply APT2; assumption. }
  split; [exact HWF|]. split; [exact HAP|].
  split.
  { intros t H' [<-|Ht] HH'; [| apply THA; assumption]. unfold t_hi. cbn [t_lo t_len t_lit t_kind].
    destruct (HAP H H' HH HH') as [<-|X]; [left; repeat split; lia| right; lia]. }
  cbn [v_stk v_img v_eb v_ghost v_tr v_hulls v_unit v_add_sub]. repeat split; try assumption; try lia;
    try (match goal with HU : v_unit v ?U9 ?n9 |- _ => ddestruct (UW U9 n9 HU) as (? & ? & ? & ? & ?); assumption end).
  - intros t [<-|Ht] TC; [unfold t_hi; cbn [t_lo t_len]| apply BANDCS; assumption]. lia.
  - constructor; [| exact TND]. intros HIn. specialize (APT _ HIn). unfold t_hi in APT. cbn [t_lo t_len] in APT. lia.
  - (* [comment removed for export] *)
    intros t U9 n9 [<-|Ht] TLt HU9; [cbn in TLt; discriminate| exact (UT t U9 n9 Ht TLt HU9)].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition trange_eqb (a b : trange) : bool :=
  (t_lo a =? t_lo b) && (t_len a =? t_len b).

Definition v_remove (v : vst) (lo : Z) (gh : list (Z * Z)) : vst := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(74.(1?.$?.Lt,$?.(6?.(26.(16.R1.)O2.))(11.O3.))(35.O3.)(1<.(19.$4.$4.)O1.(20.O3.))(5.O3.)(8.O3.)(40.O3.)(43.O3.)(46.O3.)(47.O3.)(32.O3.))")
(* [comment removed for export] *).

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L25358923035.11L40571964741.1100000;00CS1e1x2Hx2H0S1e1x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma sum_count_ext_in : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "PP,Px,$4.$13.PQ,Px,$4.$13.Pl,(61.(19.(30.&40.)(30.&40.)))P,Pe,(19.(30.&40.)(30.&40.))Px,$4.P,(10.(19.(30.&40.)(30.&40.))R2.R3.)P,(1.(2.(83.R3.)R2.)(6.R2.(<.(83.R3.)(84.R3.))))(12.$13.A1.R7.R3.A1.R6.R3.)(12.$4.(6>.R4.R2.)(6>.R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros P Q l H. induction l as [|e r IH]; [reflexivity|]. cbn [sum_count].
  rewrite (IH ltac:(intros e0 x Hin Hx; apply (H e0 x); [now right| assumption])). unfold iv_count.
  rewrite (BackingAlgebra.zcount_ext P Q); [reflexivity|]. intros x Hx. apply (H e x); [now left|]. pose proof (S_range e). rewrite Z2Nat.id in Hx by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0030>L15043407825.4L21811464176.8L37876706212.800000100=00KSS1P1e1r1a2IHS1P1e1r1a2IH1H". (* [comment removed for export] *)
#[using="Type"] Lemma sum_count_remove_le : forall P l a, sum_count P (map_remove l a) <= sum_count P l.
Proof.
  intros P l a. unfold map_remove. induction l as [|e r IH]; cbn; [lia|].
  pose proof (BackingAlgebra.zcount_nonneg P (B e) (Z.to_nat (S e))). unfold iv_count in *.
  destruct (negb (bv_eqb (fst e) a)); cbn [sum_count]; unfold iv_count; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00d0@L11424775649.100L13058012530.108L13058408412.97 L13060160071.98 L13060471105.93 L16002239660.99 L18926759799.98 L18928845742.96 L18928845742.97 L18933043916.95 L18933043916.96 L21303640324.75 L22831240455.105L23144198646.91 L24711450387.110L24711450387.113L24816150268.97 L25963904667.94 L25964171064.96 L26553311493.5  L26890139629.90 L27998384744.107L27998384744.111L30493818264.96 L36417483129.105L39147364409.99 L44820861986.90 L44888098779.81 L47966040186.96 L51851018037.100L52427764692.94 L52553944276.108L55117688560.83 L59308585732.109L59308585732.112L59308660947.112L59308730611.108L59308910835.109L59310684874.96 L59310684883.111L59315137787.107L59315137787.84 L60803539096.105L61929571768.76 L63368429084.94 L63368447790.95 L63842446571.110L65616925470.107L66086610871.95 L66622374278.91 L68044391932.96 L9658772623.109 00000I00[00m01?01Q01m02@02S02f03903L03a04?04]05=05[06906Z07@07U07h08J08o09G09_0:@0:S0:j0;?0;N0;d0<E0<]0=B0=e0>N0>j0?I0?b0@>0@[0A<0AT0Al0B?0BR0C00CH0C^0D;0DT0E6S3hAR1t1U3T681n5TBAND3ACBS3hAR1t1U3T681n2W1S3hAR1t1U3T681n2W1S3hAR1t1U3T681n2W1S3hAR1t1U3T681n2W1S3hAR1v2mo1t1U3T681n1h2EB2SRS3hAR1t1U3T681n1p1rS3hAR1t1U3T681n1p1rS3hAR1t1U3T681n1p1rS3hAR1t1U3T681n1p1rS3hAR1t1U3T681n1p1rS3hAR1t1U3T681n2W12W2S3hAR1t1U3T681n2U92n92e02A12A2S3hAR2AL1t1U3T681n4IMG24IMG41pS3hAR1t1U3T681n2lo2hi2LH1e2E12E2S3hAR1t1U3T681n2t'3TL01e2E12E2S3hAR1t1U3T681n1p1r2X11H2H02H1S3hAR1t1U3T681n3ACB1p2t'2X12X22APS3hAR1t1U3T681n5TBAND3ACB1p1r2RB2P02P1S3hAR2t'4TLO03TL03THIS3hAR1t1U3T681n1p1HS3hAR1t1U3T681n2U92n92e02A12A23NP9S3hAR1t1U3T681n1e1r2R12R22EP2e02A12A2S3hAR1t1U3T681n1p1r1H2H1S3hAR1t1U3T681n1e1x2Hx1HS3hAR1t1U3T681n1p1r2X21H2H02H12H2S3hAR1t1U3T681n1p1HS3hAR1t1U3T681n3ACB1e1XS3hAR1t1U3T681n2W12W2S3hAR1t1U3T681nS3hAR1t1U3T681n1p1r2RBS3hAR1t1U3T681n1x1q2Q12Q21r2R12R2S3hAR1t1U3T681n3ACB2t'1XS3hAR1t1U3T681n3ACB2lo2hi2LH2AP2E22E1S3hAR1t1U3T681n3ACB2t'2AP3TL02E22E1S3hAR1t1U3T681n3ACB1e1r2R12R22R32EP2A12A2S3hAR1t3T683ACB1e1x2Hx2Rt2APS3hAR1t3T682W13ACB2U92n91x2Hx1XS3hAR1t1U3T681n2W13ACB2APS3hAR1t3T683ACB1e1x2Hx2R32RtS3hAR1t3T682U92n92A13NP91X2A2S3hAR1t1U3T681n2W13ACB1e3EB12ES1XS3hAR1t1U3T681n1e1x2Hx1HS3hAR1t1U3T681n2W02W12W2S3hAR1t1U3T681n1p1rS3hAR1t1U3T681n1p1rS3hAR1t1U3T681n1e1x2Hx1r2R12R2S3hAR1t3T682U92n91x2Hx1XS3hAR1t1U3T681n1p1r2RBS3hAR1v1t1U3T681n4STK04STK21pS3hAR1t1U3T681n1p2t01H2H1S3hAR1t1U3T681n1e1r2R12R22e02A12A2". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_munmap : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pt,$?.P,(6;.R3.R2.)P,(12.$4.(65.VAL,)+7???8000.)P,(10.$?.R3.(11.R5.))P,(12.$13.(34.R4.)$15.)P,(12.$38.(39.R5.)$3>.)P,(2.=(16.R6.))P,(12.$13.(14.R7.)$15.)P,Pt',$?.P,(10.$?.R1.(11.R;.))P,(12.$4.(16.R2.)(16.R:.))(12.$?.R3.R;.)P,(2.(<.(40.R;.)(56.+1000.(57.(85.R;.(16.R9.)(18.(19.$4.$4.)(1:.$4.$4.(16.R9.)(1>.R9.))(86.(19.$4.$4.)))))))$54.)(1.(6;.(85.R<.(16.R:.)(18.(19.$4.$4.)(1:.$4.$4.(16.R:.)(1>.R:.))(86.(19.$4.$4.))))(87.(16.R:.)(1>.R:.)R;.))(12.$13.(88.(5:.(53.R;.))(76.&40.(16.R:.))(76.&40.(1>.R:.)))$15.))")
(* [comment removed for export] *).
Proof.
  intros v mo t K ASB Ht TLIT TK T68 TCS UNIQ BUD.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  pose proof (BANDCS t Ht TCS) as TBAND.
  pose proof (proj1 (Forall_forall _ _) TB t Ht) as (TC & TLH & TKF). rewrite TK in TKF. destruct TKF as [TCN TCL].
  specialize (TLH TLIT).
  pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (W0 & W1 & W2 & W3 & W4 & W5).
  aceilb. unfold t_hi in *.
  set (U := t_lo t) in *. set (n := t_len t) in *.
  assert (UZ : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  split; [| apply haslit_map_has; exact TLH].
  set (v' := v_remove v U [(U, n)]).
  (* [comment removed for export] *)
  assert (MAP : forall e, In e (vm_maps (m_vmmaps mo)) -> e = (Z_to_bv 64 U, Z_to_bv 64 n) \/ eB e + eS e <= U \/ U + n <= eB e).
  { intros e He. destruct (MSEP e _ He TLH) as [E|X]; [left; exact E| right]. cbn [fst snd] in X. rewrite UZ, NZ in X. lia. }
  assert (BASEU : forall e, In e (vm_maps (m_vmmaps mo)) -> bv_unsigned (fst e) = U -> 0 < eS e -> e = (Z_to_bv 64 U, Z_to_bv 64 n)).
  { intros e He EB1 ES. destruct (MAP e He) as [E|X]; [exact E| exfalso; lia]. }
  assert (TAP : forall t', In t' (v_tr v) -> t' = t \/ t_lo t' + t_len t' <= U \/ U + n <= t_lo t').
  { intros t' Ht'. destruct (APT2 t' t Ht' Ht) as [E|X]; [left; exact E| right]. unfold t_hi in X. lia. }
  assert (TRR : forall t', In t' (v_tr v') <-> In t' (v_tr v) /\ t' <> t).
  { intros t'. subst v'. cbn [v_tr v_remove]. rewrite filter_In. split.
    - intros [H1 H2]. split; [exact H1|]. intros ->. subst U. rewrite Z.eqb_refl in H2. discriminate.
    - intros [H1 H2]. split; [exact H1|]. destruct (Z.eqb_spec (t_lo t') U); [| reflexivity]. exfalso. apply H2. apply UNIQ; assumption. }
  assert (TAP' : forall t', In t' (v_tr v') -> t_lo t' + t_len t' <= U \/ U + n <= t_lo t').
  { intros t' Ht'. apply TRR in Ht'. destruct Ht' as [Ht' NE]. destruct (TAP t' Ht') as [E|X]; [contradiction| exact X]. }
  (* [comment removed for export] *)
  unfold munmap_model. cbv zeta. unfold with_mmap_destroyed. rewrite UZ, NZ.
  set (h := m_vmmaps mo). set (mo' := vm_forget_range _ _ _).
  assert (PM : m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (map_remove (vm_maps h) (Z_to_bv 64 U)) (maps_subtract (vm_noaccess h) U (U + n)) (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)) by reflexivity.
  assert (PL : m_vm_lazy mo' = maps_subtract (m_vm_lazy mo) U (U + n)) by (subst mo'; rewrite m_vm_lazy_vm_forget_range; reflexivity).
  assert (MATOUT : forall p, vgood v p -> bv_unsigned p + 4096 <= U \/ U + n <= bv_unsigned p).
  { intros p G. unfold vgood, vgood_b in G. apply Bool.orb_true_iff in G. destruct G as [G|G]; apply existsb_exists in G; ddestruct G as (r & Hr & X).
    - unfold pg_shadow_b in X. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
      apply Z.leb_le in X1. apply Z.leb_le in X2. apply Z.eqb_eq in X3.
      assert (RB : 0 <= fst r /\ fst r + snd r <= 2^47).
      { unfold csranges in Hr. cbn in Hr. destruct Hr as [<-|[<-|Hr]]; cbn [fst snd].
        - lia. - rewrite IMG0, IMG1. lia.
        - apply in_app_iff in Hr. destruct Hr as [Hr|Hr].
          + apply in_map_iff in Hr. ddestruct Hr as (t0 & <- & Ht0). apply filter_In in Ht0. destruct Ht0 as [Ht0 _].
            pose proof (proj1 (Forall_forall _ _) TWF t0 Ht0) as (? & ? & ? & _). cbn [fst snd]. unfold t_hi in *. lia.
          + pose proof (proj1 (Forall_forall _ _) GWF r Hr) as (? & ? & ?). lia. }
      unfold zpb, shadow_of in X1, X2. rewrite ASB in X1, X2.
      assert (P0 : 0x7fff8000 <= bv_unsigned p).
      { pose proof (Z.div_pos (fst r) 8 ltac:(lia) ltac:(lia)).
        pose proof (Z.div_mod (2147450880 + fst r / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + fst r / 8) 4096 ltac:(lia)). lia. }
      assert (P1 : bv_unsigned p + 4096 <= 0x10007fff8000).
      { assert ((fst r + snd r - 1) / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
        pose proof (Z.div_mod (2147450880 + (fst r + snd r - 1) / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (2147450880 + (fst r + snd r - 1) / 8) 4096 ltac:(lia)).
        pose proof (Z.div_mod (bv_unsigned p) 4096 ltac:(lia)). rewrite X3 in *. lia. }
      lia.
    - unfold lazyranges in Hr. apply in_map_iff in Hr. ddestruct Hr as (t' & <- & Ht'). apply filter_In in Ht'. destruct Ht' as [Ht' TK'].
      unfold pg_inside_b in X. cbn [fst snd] in X. apply andb_prop in X. destruct X as [X _]. apply andb_prop in X. destruct X as [X1 X2].
      apply Z.leb_le in X1. apply Z.leb_le in X2. destruct (TAP t' Ht') as [->|AP]; [unfold is_lazy_cs in TK'; rewrite TK in TK'; discriminate| lia]. }
  assert (PT : m_vm_materialized mo' = m_vm_materialized mo).
  { subst mo'. rewrite m_vm_materialized_vm_forget_range, m_vm_materialized_with_vmmaps.
    rewrite forallb_filter_id; [reflexivity|]. apply forallb_forall. intros p Hp.
    pose proof (MATOUT p (proj1 (Forall_forall _ _) GD p Hp)) as X. unfold page_outside_range.
    apply Bool.negb_true_iff. apply Bool.andb_false_iff. destruct X; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; lia. }
  assert (PH : m_halted mo' = m_halted mo) by (subst mo' h; destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity).
  ddestruct WF as (W1' & W2' & W3' & W4').
  assert (WF' : model_ivs_wf mo').
  { unfold model_ivs_wf. rewrite PM, PL. cbn [vm_maps vm_noaccess]. split; [apply ivs_wf_remove; exact W1'|]. split; [| split; [| exact W4']]; apply maps_subtract_wf; try assumption; lia. }
  assert (CSR : forall r, In r (csranges v) -> In r (csranges v')).
  { intros r Hr. unfold csranges in *. subst v'. cbn [v_stk v_img v_tr v_ghost v_remove]. cbn [v_stk v_img] in Hr.
    destruct Hr as [Hr|[Hr|Hr]]; [left; exact Hr| right; left; exact Hr| right; right].
    apply in_app_iff in Hr. apply in_app_iff. destruct Hr as [Hr|Hr]; [| right; apply in_app_iff; right; exact Hr].
    apply in_map_iff in Hr. ddestruct Hr as (t' & <- & Ht'). apply filter_In in Ht'. destruct Ht' as [Ht' TC'].
    destruct (TAP t' Ht') as [->|AP].
    - right. apply in_app_iff. left. left. reflexivity.
    - left. apply in_map_iff. exists t'. split; [reflexivity|]. apply filter_In. split; [| exact TC'].
      apply (proj2 (TRR t')). split; [exact Ht'|]. intros ->. lia. }
  assert (LZR : forall r, In r (lazyranges v) -> In r (lazyranges v')).
  { intros r Hr. unfold lazyranges in *. subst v'. cbn [v_tr v_remove].
    apply in_map_iff in Hr. ddestruct Hr as (t' & <- & Ht'). apply filter_In in Ht'. destruct Ht' as [Ht' TK'].
    apply in_map_iff. exists t'. split; [reflexivity|]. apply filter_In. split; [| exact TK'].
    apply (proj2 (TRR t')). split; [exact Ht'|]. intros ->. unfold is_lazy_cs in TK'. rewrite TK in TK'. discriminate. }
  assert (VCS : forall y, vcs v' y -> vcs v y).
  { intros y [Y|[Y|(t' & Ht' & TC' & R)]]; [left; exact Y| right; left; exact Y| right; right]. exists t'. split; [| auto].
    exact (proj1 (proj1 (TRR t') Ht')). }
  unfold HKv. rewrite PM, PL, PT, PH. cbn [vm_maps vm_noaccess vm_reserved vm_limit].
  split; [exact Hh|]. split; [exact ND|].
  split. { apply Forall_forall. intros p Hp. apply (vgood_mono v); [exact CSR| exact LZR|]. exact (proj1 (Forall_forall _ _) GD p Hp). }
  split.
  { intros x AOK PIR. apply (vgood_mono v); [exact CSR| exact LZR|]. apply LZ.
    - destruct AOK as [CX|[(c & Cc & E)|IM]]; [left; apply VCS; exact CX| right; left; exists c; split; [apply VCS; exact Cc| exact E]| right; right; exact IM].
    - apply page_in_ranges_true in PIR. ddestruct PIR as (q & Hq & Q1 & Q2).
      destruct (maps_subtract_pieces _ _ _ q W3' Hq) as (r & Hr & R1 & R2 & R3).
      apply (proj2 (page_in_ranges_true _ _)). exists r. split; [exact Hr| lia]. }
  split; [exact LIM|].
  split. { (* [comment removed for export] *)
    rewrite (eager_bytes_sem mo' WF'). rewrite PM, PL. cbn [vm_maps vm_noaccess]. cbn [v_eb v_remove].
    rewrite (eager_bytes_sem mo (conj W1' (conj W2' (conj W3' W4')))) in EB. fold h in EB.
    ddestruct (maps_subtract_sem (vm_noaccess h) U (U + n) W2' ltac:(lia)) as (_ & _ & CN).
    ddestruct (maps_subtract_sem (m_vm_lazy mo) U (U + n) W3' ltac:(lia)) as (_ & _ & CL).
    rewrite (sum_count_ext_in (fun x => negb (covered (maps_subtract (vm_noaccess h) U (U + n) ++ maps_subtract (m_vm_lazy mo) U (U + n)) x))
                             (fun x => negb (covered (vm_noaccess h ++ m_vm_lazy mo) x))).
    2:{ intros e x He Hx. apply in_map_remove in He. destruct He as [He NE]. unfold B, S in Hx.
        assert (OUT : in_rng U (U + n) x = false).
        { destruct (MAP e He) as [->|X]; [exfalso; apply NE; reflexivity|]. unfold in_rng. apply Bool.andb_false_iff.
          destruct X; [left; apply Z.leb_gt| right; apply Z.ltb_ge]; lia. }
        rewrite !covered_app, CN, CL, OUT. cbn [negb andb]. rewrite !Bool.andb_true_r. reflexivity. }
    pose proof (sum_count_remove_le (fun x => negb (covered (vm_noaccess h ++ m_vm_lazy mo) x)) (vm_maps h) (Z_to_bv 64 U)) as SR.
    match goal with |- ?G => idtac "MG" G end. match type of SR with ?T => idtac "SR" T end. match type of EB with ?T => idtac "EB" T end. subst v'. cbn [v_eb v_remove]. lia. }
  split; [subst v'; cbn [v_eb v_remove]; exact BUD|].
  split; [exact WF'|].
  split.
  { (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - apply Forall_forall. intros t' Ht'. pose proof (TAP' t' Ht') as AP. apply TRR in Ht'. destruct Ht' as [Ht' NE].
      pose proof (proj1 (Forall_forall _ _) TB t' Ht') as (F1 & F2 & F3). pose proof (proj1 (Forall_forall _ _) TWF t' Ht') as (TLO0 & TL0 & THI & _).
      unfold t_hi in THI. 
      split.
      { apply covers_remove; [exact F1|]. intros e He E1 E2 EQ. unfold t_hi in E2.
        assert (EBU : bv_unsigned (fst e) = U) by (rewrite EQ; exact UZ).
        pose proof (BASEU e He EBU ltac:(lia)) as ->. cbn [fst snd] in E1, E2. rewrite ?UZ, ?NZ in E1. rewrite ?UZ, ?NZ in E2. lia. }
      split.
      { intros L. apply haslit_remove; [exact (F2 L)|]. intros EQ. apply (f_equal bv_unsigned) in EQ. rewrite UZ in EQ. rewrite u64_lit in EQ by (clear - TLO0 TL0 THI; lia).
        apply NE. apply UNIQ; [exact Ht'| exact EQ]. }
      destruct (t_kind t').
      + destruct F3 as [G1 G2]. split; apply clear_subtract; assumption.
      + apply clear_subtract; assumption.
      + exact I.
    - intros e He. destruct (maps_subtract_pieces _ _ _ e W2' He) as (r & Hr & R1 & R2 & R3).
      pose proof (maps_subtract_pos _ _ _ e W2' NZN He) as EP.
      ddestruct (TN r Hr) as (e0 & He0 & A1 & A2).
      exists e0. split; [| lia]. apply in_map_remove. split; [exact He0|]. intros EQ.
      assert (EBU : bv_unsigned (fst e0) = U) by (rewrite EQ; exact UZ).
      pose proof (BASEU e0 He0 EBU ltac:(lia)) as E0. rewrite E0 in A1, A2. cbn [fst snd] in A1, A2. rewrite ?UZ, ?NZ in A1. rewrite ?UZ, ?NZ in A2. lia.
    - intros e He. destruct (maps_subtract_pieces _ _ _ e W3' He) as (r & Hr & R1 & R2 & R3).
      pose proof (maps_subtract_pos _ _ _ e W3' NZL He) as EP.
      ddestruct (TL r Hr) as (e0 & He0 & A1 & A2).
      exists e0. split; [| lia]. apply in_map_remove. split; [exact He0|]. intros EQ.
      assert (EBU : bv_unsigned (fst e0) = U) by (rewrite EQ; exact UZ).
      pose proof (BASEU e0 He0 EBU ltac:(lia)) as E0. rewrite E0 in A1, A2. cbn [fst snd] in A1, A2. rewrite ?UZ, ?NZ in A1. rewrite ?UZ, ?NZ in A2. lia.
    - (* [comment removed for export] *)
      intros U9 n9 HU9. ddestruct (THL U9 n9 HU9) as (e0 & He0 & A1 & A2). pose proof (UW U9 n9 HU9) as (NP9 & _).
      exists e0. split; [| lia]. apply in_map_remove. split; [exact He0|]. intros EQ.
      assert (EBU : bv_unsigned (fst e0) = U) by (rewrite EQ; exact UZ).
      pose proof (BASEU e0 He0 EBU ltac:(lia)) as E0. rewrite E0 in A1, A2. cbn [fst snd] in A1, A2. rewrite ?UZ, ?NZ in A1. rewrite ?UZ, ?NZ in A2.
      destruct (UT t U9 n9 Ht TLIT HU9) as [X|X]; unfold t_hi in X; subst U n; lia.
    - ddestruct TEM as (UNC & MPOS & LZK & MX & MH). split; [| split].
      + (* [comment removed for export] *)
        intros U9 n9 HU9 APU x Hx. pose proof (UW U9 n9 HU9) as (NP9 & _).
        apply ncov_subtract_keep; [exact W2'| lia| |].
        * apply (UNC U9 n9 HU9); [| exact Hx]. intros t' Ht'. destruct (TAP t' Ht') as [->|X].
          -- exact (UT t U9 n9 Ht TLIT HU9).
          -- apply APU. apply (proj2 (TRR t')). split; [exact Ht'|]. intros ->. unfold t_hi in *. subst U n. pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (_ & TP & _). lia.
        * destruct (UT t U9 n9 Ht TLIT HU9) as [X|X]; unfold t_hi in X; subst U n; lia.
      + intros e He. apply in_map_remove in He. exact (MPOS e (proj1 He)).
      + split; [| split].
        * (* [comment removed for export] *)
          intros e He x Hx. destruct (maps_subtract_pieces _ _ _ e W3' He) as (r & Hr & R1 & R2 & R3).
          destruct (LZK r Hr x ltac:(lia)) as [(t0 & Ht0 & TLt & Rt)|X]; [| right; exact X].
          left. exists t0. split; [| split; [exact TLt| exact Rt]]. apply (proj2 (TRR t0)). split; [exact Ht0|]. intros ->. unfold t_hi in Rt. subst U n. lia.
        * (* [comment removed for export] *)
          intros e He x Hx. apply in_map_remove in He. destruct He as [He NE].
          destruct (MX e He x Hx) as [(t0 & Ht0 & TLt & Rt)|X]; [| right; exact X].
          left. exists t0. split; [| split; [exact TLt| exact Rt]]. apply (proj2 (TRR t0)). split; [exact Ht0|]. intros ->.
          destruct (MAP e He) as [E|AP]; [apply NE; rewrite E; reflexivity|]. unfold t_hi in Rt. subst U n. lia.
        * (* [comment removed for export] *) intros e H He HH M1 M2. apply in_map_remove in He. exact (MH e H (proj1 He) HH M1 M2).
    - unfold map_remove. apply NoDup_filter. exact MND.
    - intros e1 e2 H1 H2. apply in_map_remove in H1. apply in_map_remove in H2. apply MSEP; tauto.
    - intros e He. eapply maps_subtract_pos; [exact W2'| exact NZN| exact He].
    - intros e He. eapply maps_subtract_pos; [exact W3'| exact NZL| exact He].
    - ddestruct BANDM as (B1 & B2 & B3).
      assert (CRM : forall lo hi, covers (vm_maps h) lo hi -> lo < hi -> (hi <= U \/ U + n <= lo) -> covers (map_remove (vm_maps h) (Z_to_bv 64 U)) lo hi).
      { intros lo hi C LH AP. apply covers_remove; [exact C|]. intros e He E1 E2 EQ.
        assert (EBU : bv_unsigned (fst e) = U) by (rewrite EQ; exact UZ).
        pose proof (BASEU e He EBU ltac:(lia)) as ->. cbn [fst snd] in E1, E2. rewrite ?UZ, ?NZ in E1. rewrite ?UZ, ?NZ in E2. lia. }
      split; [| split]; (apply CRM; [assumption| lia| unfold t_hi in TBAND; lia]). }
  split.
  { (* [comment removed for export] *)
    split; [| exact (conj CE2 (conj CE3 CE4))].
    intros e He R1 R2. apply CE1; [| exact R1| exact R2]. apply in_app_iff in He. apply in_app_iff.
    destruct He as [He|He]; [left; exact He| right]. apply in_map_remove in He. exact (proj1 He). }
  split; [exact RS|]. split; [exact RC|]. split; [| exact AT].
  (* [comment removed for export] *)
  split. { apply Forall_forall. intros t' Ht'. apply (proj1 (Forall_forall _ _) TWF). exact (proj1 (proj1 (TRR t') Ht')). }
  split. { intros t1 t2 H1 H2. apply APT2; [exact (proj1 (proj1 (TRR t1) H1))| exact (proj1 (proj1 (TRR t2) H2))]. }
  split; [exact HWF|]. split; [exact HAP|].
  split. { intros t' H Ht' HH. apply THA; [exact (proj1 (proj1 (TRR t') Ht'))| exact HH]. }
  subst v'. cbn [v_stk v_img v_eb v_ghost v_tr v_hulls v_unit v_remove]. repeat split; try assumption;
    try (match goal with HU : v_unit v ?U9 ?n9 |- _ => ddestruct (UW U9 n9 HU) as (? & ? & ? & ? & ?); assumption end).
  - constructor; [cbn [fst snd]; lia| exact GWF].
  - intros t' Ht' TC'. apply filter_In in Ht'. apply BANDCS; [exact (proj1 Ht')| exact TC'].
  - apply NoDup_filter. exact TND.
  - (* [comment removed for export] *) intros t' U9 n9 Ht' TLt HU9. apply filter_In in Ht'. exact (UT t' U9 n9 (proj1 Ht') TLt HU9).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00>0?L17302396704.52L17304280759.53L17304559399.51L2424873429.52 L2427167186.51 L2427412546.53 L29882994757.53L29883273685.51L44894663667.56L60093563309.53L60093874237.51L60095774778.52L65278115055.51L65278328191.5300000A00R00c01101?01M01[01i02L02]02n03?03M03[S3hAR1t1U1n2U02W0S3hAR1t1U1n2U02W0S3hAR1t1U1n2U02W0S3hAR1t1U1n2N0S3hAR1t1U1n2N0S3hAR1t1U1n2N0S3hAR1t1U1n2U0S3hAR1t1U1n2U0S3hAR2AL1t1U1n2U02U13IMT3ACB1e1H2H0S3hAR1t1U1n2U12W2S3hAR1t1U1n2U12W2S3hAR1t1U1n2U12W2S3hAR1t1U1n2U1S3hAR1t1U1n2U1". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_madvise : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pt,$?.PU,$4.Pn,$4.P,(6;.R5.R4.)P,(10.$?.R4.(11.R6.))P,(12.$38.(39.R5.)$79.)P,(12.$13.(34.R6.)$15.)P,(2.(16.R7.)R6.)P,(2.(<.R7.R6.)(17.R8.))P,(12.$4.(27.R8.+1000.)=)P,(12.$4.(27.R8.+1000.)=)P,(6.=R9.)(1.(12.$13.(89.(53.R=.)(76.&40.R;.)(76.&40.R:.))$15.)(6;.R>.(8:.R=.(76.&40.R;.)(76.&40.R:.))))")
(* [comment removed for export] *).
Proof.
  intros v mo t U n K Ht TK TLIT U0 U1 UAL NAL N0.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & CE & RS & RC & VW & AT).
  pose proof VW as (TWF & _).
  pose proof (proj1 (Forall_forall _ _) TB t Ht) as (TC & TLH & TKF). rewrite TK in TKF.
  pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (W0 & W1 & W2 & W3 & W4 & W5 & IMT).
  aceilb. unfold t_hi in *.
  assert (MC : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 U) (Z_to_bv 64 n) = true).
  { apply covers_map_contains; [lia| lia| lia|]. eapply covers_weaken; [exact TC| lia| lia]. }
  assert (RFR : region_free (vm_reserved (m_vmmaps mo)) (Z_to_bv 64 U) (Z_to_bv 64 n) = true).
  { apply clear_region_free; [lia| lia| lia|]. intros e He. destruct (RS e He). lia. }
  assert (RFN : region_free (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 U) (Z_to_bv 64 n) = true).
  { apply clear_region_free; [lia| lia| lia|]. eapply clear_weaken; [exact TKF| lia| lia]. }
  split; [unfold madvise_dontneed_ok; rewrite RFR, MC, RFN; reflexivity|].
  unfold madvise_dontneed_next.
  set (mo' := with_vm_backing (m_vm_lazy mo) _ mo).
  assert (PM : m_vmmaps mo' = m_vmmaps mo) by reflexivity.
  assert (PL : m_vm_lazy mo' = m_vm_lazy mo) by reflexivity.
  assert (PT : m_vm_materialized mo' = List.filter (page_outside_range (bv_unsigned (Z_to_bv 64 U)) (bv_unsigned (Z_to_bv 64 U) + bv_unsigned (Z_to_bv 64 n))) (m_vm_materialized mo)) by reflexivity.
  assert (PH : m_halted mo' = m_halted mo) by (subst mo'; destruct mo as [? [? ? ?] ? ? ? ? ?]; reflexivity).
  assert (PE : eager_bytes mo' = eager_bytes mo) by reflexivity.
  unfold HKv. rewrite PM, PL, PT, PH, PE.
  split; [exact Hh|]. split; [apply NoDup_filter; exact ND|].
  split. { apply Forall_forall. intros p Hp. apply filter_In in Hp. exact (proj1 (Forall_forall _ _) GD p (proj1 Hp)). }
  split; [exact LZ|]. split; [exact LIM|]. split; [exact EB|]. split; [exact BUD0|].
  split; [exact WF|].
  split; [exact (conj TB (conj TN (conj TL (conj THL (conj TEM (conj MND (conj MSEP (conj NZN (conj NZL BANDM)))))))))|].
  split; [exact CE|]. split; [exact RS|]. split; [exact RC|]. split; [exact VW| exact AT].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma HKv_vwf : forall v mo, HKv v mo -> vwf v.
Proof. intros v mo K. exact (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 K))))))))))))). Qed.

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L33097668962.2500000[S1a1n2N02e12X12Y12e22X22Y22e32X32Y31H2H02H1". (* [comment removed for export] *)
#[using="Type"] Lemma HKv_fresh_band : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.Pa,(30.&40.)Pn,(30.&40.)P,(6;.R4.R3.)P,(12.$13.(6=.(1<.(19.(30.&40.)(30.&40.))(5=.(53.R4.))(5:.(53.R4.)))R3.R2.)$15.)P,(6.=(25.&40.R3.))(0.(2.(<.(25.&40.R5.)(25.&40.R4.))+7???7000.)(2.+10007???8000.(25.&40.R5.)))")
(* [comment removed for export] *).
Proof.
  intros v mo a n K RF N0.
  dpose K as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & _ & _ & BANDM) & _).
  pose proof (region_free_clear _ a n N0 RF) as CL. apply clear_app_inv in CL. destruct CL as [_ CLM].
  ddestruct BANDM as ((e1 & He1 & X1 & Y1) & (e2 & He2 & X2 & Y2) & (e3 & He3 & X3 & Y3)).
  pose proof (CLM e1 He1). pose proof (CLM e2 He2). pose proof (CLM e3 He3). lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00@0?L18930594444.45L34211388010.46L35078968259.48L55343377636.45L59308579027.49L59315300849.46L59383492284.39L59383931429.47L59579064887.42L63368414764.48L63374718476.45L63374718476.47L68384295045.45L68384295045.47L68390598821.48L9840816384.45 00000800D00a01Y02\03S03o04`04h05205:05B06206g07`08LS3hAR2ALS3hAR2AL1c1HS3hAR2AL3IMH3AW33AW51c1i2Hi1HS3hAR2AL3IMH3AW03AW23AW33AW43AW53ACB3HG13HS13HG33HS31c1RS3hAR2AL3IMH4IMG33AW03AW23AW33AW43AW53ACB3HG13HS13HG33HS31c1R2R22H0S3hAR2AL3IMH3AW23AW33AW43AW53ACB3HG13HS13HG33HS31i2Hi1RS3hAR2AL1v3IMH4STK04STK21c1YS3hAR2AL3IMH4IMG33AW43AW53ACB1c1t1R2T02T12T22T61BS3hAR2ALS3hAR2AL1cS3hAR2ALS3hAR2ALS3hAR2AL3AW03AW23AW33AW43ACB3HG13HS13HG33HS31c1RS3hAR2AL3AW03AW23AW33AW43ACB3HG13HS13HG33HS31c1i2Hi1RS3hAR2AL4IMG33AW03AW23AW33AW43AW53ACB3HG13HS13HG33HS31c1RS3hAR2AL3IMH3AW43AW53ACB3HG13HS13HG33HS31c1R". (* [comment removed for export] *)
#[using="Type"] Theorem vcs_cs_ok : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.P,(5>.R1.)P,(8;.VAL,)P,(12.$4.(65.VAL,)+7???8000.)P,(2.(3<.VAL,)+65?000.)P,(12.$4.(27.(;.VAL,)+8.)=)P,(12.$4.(27.(=.VAL,)+8.)=)(8<.VAL,(4>.R7.))")
(* [comment removed for export] *).
Proof.
  intros v VW AW ASB IMH GA GB.
  dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  dpose AW as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5).
  aceilb. 
  assert (RNG : forall c, vcs v c -> (al_img_lo AL <= c < al_img_hi AL /\ ~ (hull64 (al_got AL) <= c < hull64 (al_got AL + 7) + 64) /\ ~ (hull64 (al_gsb AL) <= c < hull64 (al_gsb AL + 7) + 64))
                                    \/ ((0 <= c < al_img_lo AL \/ al_img_hi AL <= c < 2^47) /\ (c < 0x7fff7000 \/ 0x10007fff8000 <= c))).
  { intros c [Y|[(Y & G1 & G2)|(t & Ht & TC & R)]].
    - right. lia.
    - left. rewrite IMG0, IMG1 in Y. auto.
    - right. pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _ & _ & _ & T6). pose proof (BANDCS t Ht TC) as B.
      unfold t_hi in *. lia. }
  pose proof (hull64_le (al_got AL)) as HG1. pose proof (hull64_le (al_gsb AL)) as HS1. pose proof (hull64_le (al_got AL + 7)) as HG3. pose proof (hull64_le (al_gsb AL + 7)) as HS3.
  rewrite (hull64_al8 _ GA) in RNG, HG3. rewrite (hull64_al8 _ GB) in RNG, HS3.
  split; [| split; [| split]].
  - intros c Hc. pose proof (RNG c Hc) as R. unfold shadow_of. rewrite ASB.
    split; [lia|]. split; [apply Z.add_nonneg_nonneg; [lia| apply Z.div_pos; lia]|].
    assert (c / 8 <= 2^47 / 8) by (apply Z.div_le_mono; lia). change (2^47 / 8) with 17592186044416 in H.
    split; [lia|]. intros Hs. pose proof (RNG _ Hs) as R2. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). lia.
  - intros i Hi. split; intros Hc; pose proof (RNG _ Hc) as R; lia.
  - intros c i Hc Hi. pose proof (RNG c Hc) as R. unfold shadow_of. rewrite ASB. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). lia.
  - rewrite ASB. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0040?L14424486271.7 L17444254491.11L24925704730.4 L59329553411.9 00000;00S00T00dS1A1f1x1y1lS1A1f1l2l'3l''4IHP14IHP2SS1A1f1x1l2l'3IHP". (* [comment removed for export] *)
#[using="Type"] Lemma zsum_perm : forall {A} (f : A -> Z) l l', Permutation l l' -> zsum f l = zsum f l'.
Proof. intros A f l l' P. induction P; cbn; try lia. Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

#[using="Type"] Lemma existsb_perm : forall {A} (f : A -> bool) l l', Permutation l l' -> existsb f l = existsb f l'.
Proof.
  intros A f l l' P. destruct (existsb f l) eqn:E1; destruct (existsb f l') eqn:E2; try reflexivity.
  - apply existsb_exists in E1. ddestruct E1 as (x & Hx & Fx). assert (X : existsb f l' = true) by (apply existsb_exists; exists x; split; [eapply Permutation_in; eauto| exact Fx]). congruence.
  - apply existsb_exists in E2. ddestruct E2 as (x & Hx & Fx). assert (X : existsb f l = true) by (apply existsb_exists; exists x; split; [eapply Permutation_in; [apply Permutation_sym|]; eauto| exact Fx]). congruence.
Qed.

Definition vperm (v v' : vst) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(1.(8=.$?.(11.O2.)(11.O1.))(1.(8=.(19.$4.$4.)(43.O2.)(43.O1.))(1.(12.(61.(19.$4.$4.))(35.O1.)(35.O2.))(1.(12.(61.(19.$4.$4.))(20.O1.)(20.O2.))(1.(12.(19.$4.$4.)(5.O1.)(5.O2.))(1.(12.(19.$4.$4.)(8.O1.)(8.O2.))(1.(12.$4.(40.O1.)(40.O2.))(1.(12.$4.(46.O1.)(46.O2.))(1.(12.$4.(47.O1.)(47.O2.))(12.P,$4.P,$4.Sp(32.O1.)(32.O2.)))))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

#[using="Type"] Lemma csranges_perm : forall v v', vperm v v' -> Permutation (csranges v) (csranges v').
Proof.
  (intros v v' dd_H; ddestruct dd_H as (P & _ & _ & G & S & I & _)). unfold csranges. rewrite G, S, I. apply perm_skip. apply perm_skip.
  apply Permutation_app_tail. apply Permutation_map. unfold List.filter.
  induction P; cbn; [constructor| | |].
  - destruct (t_cs x); [apply perm_skip|]; assumption.
  - destruct (t_cs x), (t_cs y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply perm_trans; eauto.
Qed.
#[using="Type"] Lemma lazyranges_perm : forall v v', vperm v v' -> Permutation (lazyranges v) (lazyranges v').
Proof.
  intros v v' (P & _). unfold lazyranges. apply Permutation_map. unfold List.filter.
  induction P; cbn; [constructor| | |].
  - destruct (is_lazy_cs x); [apply perm_skip|]; assumption.
  - destruct (is_lazy_cs x), (is_lazy_cs y); try apply perm_swap; try apply perm_skip; apply Permutation_refl.
  - eapply perm_trans; eauto.
Qed.
#[using="Type"] Lemma vgood_perm : forall v v' p, vperm v v' -> vgood v p -> vgood v' p.
Proof.
  intros v v' p VP G. unfold vgood, vgood_b in *.
  rewrite <- (existsb_perm _ _ _ (csranges_perm v v' VP)), <- (existsb_perm _ _ _ (lazyranges_perm v v' VP)). exact G.
Qed.
#[using="Type"] Lemma vnb_perm : forall v v', vperm v v' -> vnb v' = vnb v.
Proof. intros v v' VP. unfold vnb. rewrite (zsum_perm _ _ _ (csranges_perm v v' VP)), (zsum_perm _ _ _ (lazyranges_perm v v' VP)). reflexivity. Qed.
#[using="Type"] Lemma vcs_perm : forall v v' x, vperm v v' -> vcs v x <-> vcs v' x.
Proof.
  (intros v v' x dd_H; ddestruct dd_H as (P & _ & _ & _ & S & I & _)). unfold vcs. rewrite S, I. split; intros [A|[A|(t & Ht & R)]].
  - left; exact A. - right; left; exact A. - right; right; exists t; split; [eapply Permutation_in; [exact P| exact Ht]| exact R].
  - left; exact A. - right; left; exact A. - right; right; exists t; split; [eapply Permutation_in; [apply Permutation_sym; exact P| exact Ht]| exact R].
Qed.

#[using="Type"] Theorem HKv_perm : forall v v' mo, vperm v v' -> HKv v mo -> HKv v' mo.
Proof.
  intros v v' mo VP K. dpose VP as (P & PC & HU & GH & ST & IM & EBQ & C20 & C23 & UQ).
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  assert (INt : forall t, In t (v_tr v') <-> In t (v_tr v)).
  { intros t. split; intros H; [eapply Permutation_in; [apply Permutation_sym; exact P| exact H]| eapply Permutation_in; [exact P| exact H]]. }
  assert (INc : forall c, In c (v_cover v') <-> In c (v_cover v)).
  { intros c. split; intros H; [eapply Permutation_in; [apply Permutation_sym; exact PC| exact H]| eapply Permutation_in; [exact PC| exact H]]. }
  unfold HKv. rewrite EBQ. rewrite (vnb_perm v v' VP).
  split; [exact Hh|]. split; [exact ND|].
  split; [apply Forall_forall; intros p Hp; apply (vgood_perm v v' p VP); exact (proj1 (Forall_forall _ _) GD p Hp)|].
  split; [intros x AOK PIR; apply (vgood_perm v v' _ VP); apply LZ; [| exact PIR];
          destruct AOK as [A|[(c & Cc & E)|A]]; [left; apply (vcs_perm v v' x VP); exact A| right; left; exists c; split; [apply (vcs_perm v v' c VP); exact Cc| exact E]| right; right; exact A]|].
  split; [exact LIM|]. split; [exact EB|]. split; [exact BUD0|]. split; [exact WF|].
  split.
  { unfold vm_table. rewrite ?HU. split; [apply Forall_forall; intros t Ht; apply (proj1 (Forall_forall _ _) TB); apply INt; exact Ht|].
    split; [exact TN|]. split; [exact TL|]. rewrite UQ. split; [exact THL|].
    split; [ddestruct TEM as (UNC & MPOS & LZK & MX & MH); split; [intros U9 n9 HU9 APU; apply (UNC U9 n9 HU9); intros t Ht; apply APU; apply INt; exact Ht| split; [exact MPOS| split; [| split; [| exact MH]]]];
            [ intros e He x Hx; destruct (LZK e He x Hx) as [(t0 & Ht0 & TLt & Rt)|X]; [left; exists t0; split; [apply INt; exact Ht0| split; [exact TLt| exact Rt]]| right; exact X]
            | intros e He x Hx; destruct (MX e He x Hx) as [(t0 & Ht0 & TLt & Rt)|X]; [left; exists t0; split; [apply INt; exact Ht0| split; [exact TLt| exact Rt]]| right; exact X] ]|].
    split; [exact MND|]. split; [exact MSEP|]. split; [exact NZN|]. split; [exact NZL| exact BANDM]. }
  split.
  { unfold vcensus. split; [intros e He R1 R2; ddestruct (CE1 e He R1 R2) as (c & Hc & X); exists c; split; [apply INc; exact Hc| exact X]|].
    split; [intros c Hc; apply CE2; apply INc; exact Hc|].
    rewrite <- (zsum_perm _ _ _ PC), C20. rewrite <- (zsum_perm _ _ _ PC), C23. split; [exact CE3| exact CE4]. }
  split; [exact RS|]. split; [exact RC|]. split; [| exact AT].
  unfold vwf. rewrite ?HU, ?ST, ?IM, ?GH, ?UQ.
  split; [apply Forall_forall; intros t Ht; apply (proj1 (Forall_forall _ _) TWF); apply INt; exact Ht|].
  split; [intros t1 t2 H1 H2; apply APT2; apply INt; assumption|].
  split; [exact HWF|]. split; [exact HAP|].
  split; [intros t H Ht HH; apply THA; [apply INt; exact Ht| exact HH]|].
  repeat split; try assumption; try (intros t Ht TC; apply BANDCS; [apply INt; exact Ht| exact TC]);
    try (match goal with HU9 : v_unit v ?U9 ?n9 |- _ => ddestruct (UW U9 n9 HU9) as (? & ? & ? & ? & ?); assumption end).
  - rewrite EBQ. exact EB0.
  - eapply Permutation_NoDup; [exact P| exact TND].
  - intros t U9 n9 Ht TLt HU9. apply (UT t U9 n9); [apply INt; exact Ht| exact TLt| exact HU9].
Qed.

#[using="Type"] Lemma vranges_ok_perm : forall v v', vperm v v' -> vranges_ok v -> vranges_ok v'.
Proof.
  (intros v v' VP dd_H; ddestruct dd_H as (A & B & C)). split; [exact A|]. split.
  - apply Forall_forall. intros r Hr. apply (proj1 (Forall_forall _ _) B). eapply Permutation_in; [apply Permutation_sym; apply csranges_perm; exact VP| exact Hr].
  - apply Forall_forall. intros r Hr. apply (proj1 (Forall_forall _ _) C). eapply Permutation_in; [apply Permutation_sym; apply lazyranges_perm; exact VP| exact Hr].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition v_hole (v : vst) (U n : Z) : vst := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(74.(11.O3.)(86.(19.$4.$4.))(20.O3.)(5.O3.)(8.O3.)(40.O3.)(43.O3.)(46.O3.)(47.O3.)LU',$4.Ln',$4.(1.(32.O3.R2.R1.)(9.(1.(12.$4.R2.O2.)(12.$4.R1.O1.)))))")
(* [comment removed for export] *).

#[using="Type"] Lemma vranges_ok_hole : forall v U n, vranges_ok v -> vranges_ok (v_hole v U n).
Proof. intros v U n H. exact H. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma NoDup_app_intro : forall {A} (l1 l2 : list A), List.NoDup l1 -> List.NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> List.NoDup (l1 ++ l2).
Proof.
  intros A l1. induction l1 as [|x r IH]; intros l2 N1 N2 D; [exact N2|]. cbn. inversion N1; subst. constructor.
  - intros Hin. apply in_app_iff in Hin. destruct Hin as [Hin|Hin]; [contradiction| exact (D x ltac:(now left) Hin)].
  - apply IH; [assumption| assumption| intros a Ha; apply D; now right].
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0020?L35174204767.13L59314955108.1300000K00\S1a2sz2lo2hi2WF2LH2Ra2EL2ERS1a2lo2hi2LH2EL1E". (* [comment removed for export] *)
#[using="Type"] Lemma nodup_iv_subtract : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pa,(30.&40.)Psz,(30.&40.)Plo,$4.Phi,$4.P,(2.(<.(25.&40.R4.)(25.&40.R3.))(3?.+2.+40.))P,(2.R3.R2.)(36.(19.(30.&40.)(30.&40.))(8>.R6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi WF LH. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct (bv_unsigned a <? lo) eqn:EL; destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:ER; cbn [app];
    try apply Z.ltb_lt in EL; try apply Z.ltb_lt in ER; repeat constructor; cbn [In]; try tauto.
  intros [E|[]]. apply (f_equal (fun q => bv_unsigned (fst q))) in E. cbn [fst] in E. rewrite u64_lit in E by lia. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "0010?L59308730611.2700000LS1a2sz1q2X12X22QP1r2Y12Y22AP". (* [comment removed for export] *)
#[using="Type"] Lemma nodup_subtract : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "PM,(61.(19.(30.&40.)(30.&40.)))Plo,$4.Phi,$4.P,(72.R3.)P,(2.R3.R2.)P,(36.(19.(30.&40.)(30.&40.))R5.)P,(8?.R6.)P,Pe,(19.(30.&40.)(30.&40.))P,(10.(19.(30.&40.)(30.&40.))R1.R8.)(6.=(25.&40.(7.(30.&40.)(30.&40.)R2.)))(36.(19.(30.&40.)(30.&40.))(73.R8.R7.R6.))")
(* [comment removed for export] *).
Proof.
  induction M as [|[a sz] M IH]; intros lo hi WF LH ND SEP POS; [constructor|].
  apply ivs_wf_cons_inv in WF. destruct WF as [Wa WM]. inversion ND as [|? ? NIN ND']; subst. cbn [maps_subtract].
  apply NoDup_app_intro.
  - apply nodup_iv_subtract; [exact Wa| exact LH].
  - apply IH; [exact WM| exact LH| exact ND'| intros e1 e2 H1 H2; apply SEP; now right| intros e He; apply POS; now right].
  - intros q Hq1 Hq2.
    dpose (iv_subtract_pieces a sz lo hi q Wa Hq1) as (X1 & X2 & _).
    pose proof (iv_subtract_pos a sz lo hi q (POS (a, sz) ltac:(now left)) Wa Hq1) as QP.
    ddestruct (maps_subtract_pieces M lo hi q WM Hq2) as (r & Hr & Y1 & Y2 & _).
    destruct (SEP (a, sz) r ltac:(now left) ltac:(now right)) as [E|AP]; [subst r; exact (NIN Hr)|]. cbn [fst snd] in AP. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0060?L13058391648.16L13060160071.18L13060422342.17L13060474749.15L21305934984.9 L61929571768.1000000800@00H00P00^00lS1U1n2N0S1U1n2N0S1U1n2N0S1U1n2N0S1U1n2U02N02UNS1U1n2U02N02UN". (* [comment removed for export] *)
#[using="Type"] Lemma eager_destroy_le : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pmo,$6:.PU,$4.Pn,$4.P,(58.R3.)P,(2.=R3.)P,(6.=R3.)P,(6.(<.R5.R4.)(3?.+2.+40.))(1.(58.(90.R6.R5.R7.))(2.(55.(90.R6.R5.R7.))(55.R7.)))")
(* [comment removed for export] *).
Proof.
  intros mo U n WF U0 N0 UN.
  assert (UZ : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  dpose WF as (W1 & W2 & W3 & W4).
  assert (WF' : model_ivs_wf (fixrw_destroyed U n mo)).
  { unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. rewrite UZ, NZ.
    apply model_ivs_wf_vm_forget_range; [lia|]. apply model_ivs_wf_with_vmmaps; [exact WF| | |reflexivity];
      unfold mmap_fixed_destroyed_next; cbn [vm_maps vm_noaccess]; rewrite UZ, NZ; apply maps_subtract_wf; (assumption || lia). }
  split; [exact WF'|].
  rewrite (eager_bytes_sem _ WF'), (eager_bytes_sem _ WF).
  unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. unfold mmap_fixed_destroyed_next. cbn [vm_maps vm_noaccess]. rewrite UZ, NZ.
  destruct (maps_subtract_sem _ U (U + n) W1 ltac:(lia)) as (_ & SM & _).
  destruct (maps_subtract_sem _ U (U + n) W2 ltac:(lia)) as (_ & _ & CN).
  destruct (maps_subtract_sem _ U (U + n) W3 ltac:(lia)) as (_ & _ & CL).
  rewrite SM. apply sum_count_mono. intros x Hx. rewrite covered_app, CN, CL in Hx. rewrite covered_app.
  destruct (covered (vm_noaccess (m_vmmaps mo)) x), (covered (m_vm_lazy mo) x), (in_rng U (U + n) x); cbn in Hx |- *; congruence.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00P0?L10419669224.98L11422990074.86L11938148329.94L11940565167.93L12708493532.90L13057981245.94L13058012530.89L13058012530.92L13060453721.92L13060470621.84L13060470621.86L13060523131.93L17302376639.72L21064733037.92L21303640324.70L29554614475.93L32113851243.94L3422993595.94 L41982896304.92L44894274515.92L46186464917.92L51204515496.84L51852835886.86L52553944276.95L59309009780.95L60095729573.72L61255129054.94L61388613006.94L61929571768.71L63842446571.93L66218966358.93L66972341337.8900000K00\00n01@01U01a01m02902E02Q02]02i03603F03Z03i04<04O04_05105?05U05^06906S06`06n07@07T07l08I08\S3hAR1U1n1e1r2P12P21c2X12X2S3hAR1U1n3UHI3ACBS3hAR1U1n3ACB1t2APS3hAR1U1n3ACB1t2APS3hAR1U1n3ACB2U92n91XS3hAR1U1n2N0S3hAR1U1n2N0S3hAR1U1n2N0S3hAR1U1n2N0S3hAR1U1n2N0S3hAR1U1n2N0S3hAR1U1n2N0S3hAR1U1n3U68S3hAR1U1n1q1r2R1S3hAR1U1n3U682N03UCES3hAR1U1n1t3TL0S3hAR1U1n1e2R21r2P1S3hAR1U1n1e2R11r2P2S3hAR1U1n1q1r2R2S3hAR1U1n3ACB1q2R3S3hAR1U1n1q2QPS3hAR1v2mo1U1n2EB4EBLES3hAR1U1nS3hAR1U1n1x1q2Q12Q21r2R12R2S3hAR1U1n3ACB1q1x2Hx2R32RUS3hAR1U1n3UCES3hAR1U1n1t2T2S3hAR1U1n1t2T03TL0S3hAR1U1n3U682N03UCES3hAR1U1n1q1x2Hx1r2R12R2S3hAR1U1n2N03ACB2U92n91x2Hx1XS3hAR1U1n2U92n93NP9". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_destroy_sub : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.PU,$4.Pn,$4.P,(6;.R4.R3.)P,(12.$4.(65.VAL,)+7???8000.)P,(2.(3<.VAL,)+65?000.)P,(32.R7.R5.R4.)P,(2.+65?000.R6.)P,(0.(2.(<.R7.R6.)+7???7000.)(2.+10007???8000.R7.))P,Pt,$?.P,(10.$?.R1.(11.R;.))(0.(2.(<.R:.R9.)(16.R2.))(2.(17.R2.)R:.))(6;.(91.R;.R9.R8.)(90.R9.R8.R:.))")
(* [comment removed for export] *).
Proof.
  intros v mo U n K ASB IMH HUN U68 UHI APT.
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & (CE1 & CE2 & CE3 & CE4) & RS & RC & VW & AT).
  dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  ddestruct TEM as (UNC & MPOS & LZK & MX & MH).
  dpose (UW U n HUN) as (N0 & U0 & UCE & UAL & NAL).
  aceilb.
  assert (UZ : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  destruct (eager_destroy_le mo U n WF ltac:(lia) N0 ltac:(lia)) as [WF' EBLE].
  dpose WF as (W1' & W2' & W3' & W4').
  (* [comment removed for export] *)
  assert (PMM : vm_maps (m_vmmaps (fixrw_destroyed U n mo)) = maps_subtract (vm_maps (m_vmmaps mo)) U (U + n)).
  { unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. unfold mmap_fixed_destroyed_next. cbn [vm_maps]. rewrite UZ, NZ. reflexivity. }
  assert (PMN : vm_noaccess (m_vmmaps (fixrw_destroyed U n mo)) = maps_subtract (vm_noaccess (m_vmmaps mo)) U (U + n)).
  { unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. unfold mmap_fixed_destroyed_next. cbn [vm_noaccess]. rewrite UZ, NZ. reflexivity. }
  assert (PMR : vm_reserved (m_vmmaps (fixrw_destroyed U n mo)) = vm_reserved (m_vmmaps mo)).
  { unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. reflexivity. }
  assert (PML : vm_limit (m_vmmaps (fixrw_destroyed U n mo)) = vm_limit (m_vmmaps mo)).
  { unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. reflexivity. }
  assert (PL : m_vm_lazy (fixrw_destroyed U n mo) = maps_subtract (m_vm_lazy mo) U (U + n)).
  { unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. rewrite UZ, NZ. reflexivity. }
  assert (PT : m_vm_materialized (fixrw_destroyed U n mo) = List.filter (page_outside_range U (U + n)) (m_vm_materialized mo)).
  { unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. rewrite UZ, NZ. reflexivity. }
  unfold HKv. rewrite PMM, PMN, PMR, PML, PL, PT.
  split; [rewrite halted_fixrw_destroyed; exact Hh|].
  split; [apply NoDup_filter; exact ND|].
  split. { apply Forall_forall. intros p Hp. apply filter_In in Hp. exact (proj1 (Forall_forall _ _) GD p (proj1 Hp)). }
  split.
  { intros x AOK PIR. apply (LZ x AOK).
    apply page_in_ranges_true in PIR. ddestruct PIR as (q & Hq & Q1 & Q2).
    destruct (maps_subtract_pieces _ _ _ q W3' Hq) as (r & Hr & R1 & R2 & R3).
    apply (proj2 (page_in_ranges_true _ _)). exists r. split; [exact Hr| lia]. }
  split; [exact LIM|].
  split; [cbn [v_eb v_hole]; lia|].
  split; [exact BUD0|].
  split; [exact WF'|].
  split.
  { (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - apply Forall_forall. intros t Ht. pose proof (proj1 (Forall_forall _ _) TB t Ht) as (F1 & F2 & F3).
      pose proof (APT t Ht) as AP. pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & TL0 & T2 & _). unfold tfacts. unfold t_hi in *.
      split; [apply covers_subtract; [exact W1'| lia| lia| exact F1| lia]|].
      split; [intros HLt; apply haslit_subtract; [lia| lia| lia| lia| exact (F2 HLt)| lia]|].
      destruct (t_kind t).
      + destruct F3 as [G1 G2]. split; apply clear_subtract; assumption.
      + apply clear_subtract; assumption.
      + exact I.
    - intros q Hq. destruct (maps_subtract_pieces _ _ _ q W2' Hq) as (r & Hr & R1 & R2 & R3).
      pose proof (maps_subtract_pos _ _ _ q W2' NZN Hq) as QP.
      apply covers_subtract; [exact W1'| lia| lia| eapply covers_weaken; [exact (TN r Hr)| lia| lia]| lia].
    - intros q Hq. destruct (maps_subtract_pieces _ _ _ q W3' Hq) as (r & Hr & R1 & R2 & R3).
      pose proof (maps_subtract_pos _ _ _ q W3' NZL Hq) as QP.
      apply covers_subtract; [exact W1'| lia| lia| eapply covers_weaken; [exact (TL r Hr)| lia| lia]| lia].
    - (* [comment removed for export] *)
      intros U9 n9 [HU9 NE9]. pose proof (UW U9 n9 HU9) as (NP9 & _).
      apply covers_subtract; [exact W1'| lia| lia| exact (THL U9 n9 HU9)|].
      destruct (USEP U9 n9 U n HU9 HUN) as [E|X]; [exfalso; exact (NE9 E)| lia].
    - split; [| split].
      + intros U9 n9 [HU9 NE9] APU x Hx. pose proof (UW U9 n9 HU9) as (NP9 & _).
        apply ncov_subtract_keep; [exact W2'| lia| exact (UNC U9 n9 HU9 APU x Hx)|].
        destruct (USEP U9 n9 U n HU9 HUN) as [E|X]; [exfalso; exact (NE9 E)| lia].
      + intros q Hq. eapply maps_subtract_pos; [exact W1'| exact MPOS| exact Hq].
      + split; [| split; [| intros e H He []]].
        * (* [comment removed for export] *)
          intros q Hq x Hx. destruct (maps_subtract_pieces _ _ _ q W3' Hq) as (r & Hr & R1 & R2 & R3).
          destruct (LZK r Hr x ltac:(lia)) as [X|(U9 & n9 & HU9 & RU)]; [left; exact X|].
          right. dexists U9, n9. split; [| exact RU]. split; [exact HU9|]. intros [-> ->]. lia.
        * (* [comment removed for export] *)
          intros q Hq x Hx. destruct (maps_subtract_pieces _ _ _ q W1' Hq) as (r & Hr & R1 & R2 & R3).
          destruct (MX r Hr x ltac:(lia)) as [X|(U9 & n9 & HU9 & RU)]; [left; exact X|].
          right. dexists U9, n9. split; [| exact RU]. split; [exact HU9|]. intros [-> ->]. lia.
    - apply nodup_subtract; [exact W1'| lia| exact MND| exact MSEP| exact MPOS].
    - apply msep_subtract; [exact W1'| lia| exact MSEP].
    - intros e He. eapply maps_subtract_pos; [exact W2'| exact NZN| exact He].
    - intros e He. eapply maps_subtract_pos; [exact W3'| exact NZL| exact He].
    - ddestruct BANDM as (B1 & B2 & B3). repeat split; (apply covers_subtract; [exact W1'| lia| lia| assumption| lia]). }
  split.
  { (* [comment removed for export] *)
    split; [| exact (conj CE2 (conj CE3 CE4))].
    intros e He R1 R2. apply in_app_iff in He. destruct He as [He|He].
    - apply CE1; [apply in_app_iff; left; exact He| exact R1| exact R2].
    - destruct (maps_subtract_pieces _ _ _ e W1' He) as (r & Hr & P1 & P2 & P3).
      pose proof (maps_subtract_pos _ _ _ e W1' MPOS He) as EP.
      ddestruct (CE1 r ltac:(apply in_app_iff; right; exact Hr) ltac:(lia) ltac:(lia)) as (c & Hc & X1 & X2).
      exists c. split; [exact Hc| lia]. }
  split; [exact RS|]. split; [exact RC|]. split; [| exact AT].
  (* [comment removed for export] *)
  split; [exact TWF|]. split; [exact APT2|].
  split; [constructor|]. split; [intros H1 H2 []|]. split; [intros t H _ []|].
  cbn [v_stk v_img v_eb v_ghost v_tr v_hulls v_unit v_hole]. repeat split; try assumption;
    try (match goal with HU : v_unit v ?U9 ?n9 /\ _ |- _ => ddestruct (UW U9 n9 (proj1 HU)) as (? & ? & ? & ? & ?); assumption end).
  - intros U9 n9 U8 n8 [H9 _] [H8 _]. exact (USEP U9 n9 U8 n8 H9 H8).
  - intros H [].
  - intros t U9 n9 Ht TLt [HU9 _]. exact (UT t U9 n9 Ht TLt HU9).
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)


(* [comment removed for export] *)
Definition HKh (v : vst) (U n : Z) (mh : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AVm ()) "(1.(6;.(91.O4.O3.O2.)O1.)(1.(5>.O4.)(1.Pe,(19.(30.&40.)(30.&40.))PH,(19.$4.$4.)P,(10.(19.(30.&40.)(30.&40.))R2.(5:.(53.O1.)))P,(10.(19.$4.$4.)R2.(35.O4.))P,(6.(25.&40.(3.(30.&40.)(30.&40.)R4.))(<.(3.$4.$4.R3.)(7.$4.$4.R3.)))P,(6.(3.$4.$4.R4.)(<.(25.&40.(3.(30.&40.)(30.&40.)R5.))(25.&40.(7.(30.&40.)(30.&40.)R5.))))(1.(2.(3.$4.$4.R5.)(25.&40.(3.(30.&40.)(30.&40.)R6.)))(2.(<.(25.&40.(3.(30.&40.)(30.&40.)R6.))(25.&40.(7.(30.&40.)(30.&40.)R6.)))(<.(3.$4.$4.R5.)(7.$4.$4.R5.))))(1.(71.(5:.(53.O1.))O3.(<.O3.O2.))(1.(71.(5;.(53.O1.))O3.(<.O3.O2.))(71.(51.O1.)O3.(<.O3.O2.)))))))")
(* [comment removed for export] *).

#[using="Type"] Theorem HKh_kinv : forall v U n, vranges_ok v -> kinv AL (vcs v) (HKh v U n).
Proof.
  intros v U n W. pose proof (HKv_kinv (v_hole v U n) (vranges_ok_hole v U n W)) as KL. split.
  - intros mo [K _]. exact (ki_halted KL mo K).
  - intros mo [K _]. exact (ki_top KL mo K).
  - intros mo acc [K (VW0 & MH0 & C1 & C2 & C3)] OK. ddestruct (ki_mat KL mo acc K OK) as (mo' & E & K' & MM).
    exists mo'. split; [exact E|]. split; [| exact MM]. split; [exact K'|]. split; [exact VW0|].
    ddestruct MM as (_ & EV & EL & _). rewrite EV, EL. auto.
Qed.

Local Ltac2 Set LiaOrc.tbl := fun () => "0070?L14887528701.37L21303640324.23L42796375072.39L47427134892.25L51135828186.25L61929571768.24L67494645980.3700000A00U00l01501<01P01aS3hAR1q1H2M21r2R2S3hAR1U1n3U682N03UCES3hAR1q1H1r2R12R22H02H1S3hAR1U1nS3hAR1US3hAR1U1n3U682N03UCES3hAR1q1H2M11r2R1". (* [comment removed for export] *)
#[using="Type"] Theorem HKh_of_destroy : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmo,$6:.PU,$4.Pn,$4.P,(6;.R4.R3.)P,(12.$4.(65.VAL,)+7???8000.)P,(2.(3<.VAL,)+65?000.)P,(32.R7.R5.R4.)P,(2.+65?000.R6.)P,(0.(2.(<.R7.R6.)+7???7000.)(2.+10007???8000.R7.))P,Pt,$?.P,(10.$?.R1.(11.R;.))(0.(2.(<.R:.R9.)(16.R2.))(2.(17.R2.)R:.))(92.R;.R9.R8.(90.R9.R8.R:.))")
(* [comment removed for export] *).
Proof.
  intros v mo U n K ASB IMH HUN U68 UHI APT. split; [apply HKv_destroy_sub; assumption|]. split; [exact (HKv_vwf v mo K)|].
  dpose K as (_ & _ & _ & _ & _ & _ & _ & (W1 & W2 & W3 & _) & (_ & _ & _ & _ & (_ & _ & _ & _ & MH) & _) & _ & _ & _ & VW & _).
  dpose VW as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & UW & _).
  dpose (UW U n HUN) as (N0 & U0 & UCE & _). aceilb.
  assert (UZ : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  unfold fixrw_destroyed, with_mmap_destroyed. cbv zeta. model_proj. unfold mmap_fixed_destroyed_next. cbn [vm_maps vm_noaccess]. rewrite UZ, NZ.
  split.
  { (* [comment removed for export] *)
    intros q H Hq HH M1 M2. destruct (maps_subtract_pieces _ _ _ q W1 Hq) as (r & Hr & R1 & R2 & R3).
    pose proof (maps_subtract_pos _ _ _ q W1 ltac:(dpose K as (_ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & (_ & MPOS & _) & _) & _); exact MPOS) Hq) as QP.
    destruct (MH r H Hr HH ltac:(lia) ltac:(lia)). lia. }
  split; [apply clear_subtract_cut; [exact W1| lia| lia]|]. split; [apply clear_subtract_cut; [exact W2| lia| lia]| apply clear_subtract_cut; [exact W3| lia| lia]].
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080?L21303394826.11L2424962856.22 L2425231716.17 L60095625355.17L60095694003.19L60420265811.22L61929571768.12L63614397388.2200000>00N00Y00d00o01<01J01WS1U1n2U02N02UNS1U1n2U02N01x2HxS1U1n2U02N0S1U1n2U02UNS1U1n2U02UNS1U1n2U01x2HxS1U1n2U02N02UNS1U1n2U01x2Hx". (* [comment removed for export] *)
#[using="Type"] Lemma eager_rereserve_le : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pmh,$6:.PU,$4.Pn,$4.P,(58.R3.)P,(2.=R3.)P,(6.=R3.)P,(6.(<.R5.R4.)(3?.+2.+40.))P,(12.$4.(27.R6.+1000.)=)P,(12.$4.(27.R6.+1000.)=)(1.(58.(93.R8.R7.R9.))(1.(2.(55.(93.R8.R7.R9.))(55.R9.))(12.(61.(19.(30.&40.)(30.&40.)))(51.(93.R8.R7.R9.))(18.(19.(30.&40.)(30.&40.))(1:.(30.&40.)(30.&40.)(76.&40.R8.)(76.&40.R7.))(51.R9.)))))")
(* [comment removed for export] *).
Proof.
  intros mh U n WF U0 N0 UN UAL NAL.
  assert (UZ : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  dpose WF as (W1 & W2 & W3 & W4).
  assert (LI : lazy_interior (Z_to_bv 64 U) (Z_to_bv 64 n) = [(Z_to_bv 64 U, Z_to_bv 64 n)]).
  { apply lazy_interior_aligned; unfold page_size; rewrite ?UZ, ?NZ; [exact UAL| exact NAL| lia| lia]. }
  assert (PL : m_vm_lazy (norep_grant U n mh) = (Z_to_bv 64 U, Z_to_bv 64 n) :: m_vm_lazy mh).
  { unfold norep_grant, with_mmap_backing. cbv zeta. replace (mmap_noreserve_b (Z_to_bv 64 1064994)) with true by (vm_compute; reflexivity).
    model_proj. rewrite LI. reflexivity. }
  assert (WF' : model_ivs_wf (norep_grant U n mh)).
  { unfold norep_grant. cbv zeta. apply model_ivs_wf_with_mmap_backing; [rewrite UZ, NZ; lia|].
    apply model_ivs_wf_with_vmmaps; [exact WF| | | reflexivity]; cbn [vm_maps vm_noaccess];
      (apply ivs_wf_cons; [apply iv_wf_intro; rewrite UZ, NZ; lia| assumption]). }
  split; [exact WF'|]. split; [| exact PL].
  rewrite (eager_bytes_sem _ WF'), (eager_bytes_sem _ WF). rewrite PL.
  unfold norep_grant. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj. cbn [vm_maps vm_noaccess].
  cbn [sum_count]. 
  assert (Z0 : iv_count (fun x => negb (covered (((Z_to_bv 64 U, Z_to_bv 64 n) :: vm_noaccess (m_vmmaps mh)) ++ (Z_to_bv 64 U, Z_to_bv 64 n) :: m_vm_lazy mh) x))
                        (Z_to_bv 64 U, Z_to_bv 64 n) = 0).
  { unfold iv_count. apply BackingAlgebra.zcount_false. intros x Hx. unfold B, S in Hx. cbn [fst snd] in Hx. rewrite UZ, NZ, Z2Nat.id in Hx by lia.
    apply Bool.negb_false_iff. rewrite covered_app. apply Bool.orb_true_iff. left. cbn [covered existsb]. apply Bool.orb_true_iff. left.
    unfold in_iv, in_rng, B, S. cbn [fst snd]. rewrite UZ, NZ.
    apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia. }
  rewrite Z0. rewrite Z.add_0_l. apply sum_count_mono. intros x Hx.
  rewrite covered_app in Hx |- *. unfold covered in Hx |- *. cbn [existsb] in Hx.
  destruct (in_iv (Z_to_bv 64 U, Z_to_bv 64 n) x), (existsb (fun c => in_iv c x) (vm_noaccess (m_vmmaps mh))), (existsb (fun c => in_iv c x) (m_vm_lazy mh));
    cbn in Hx |- *; congruence.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Local Ltac2 Set LiaOrc.tbl := fun () => "00R0@L17302376639.84 L17304280759.85 L21303640324.82 L23321674369.93 L24122832638.101L2424860234.84  L2425350468.93  L25833299609.101L25833683028.97 L37496842517.98 L37496908180.104L40929678167.95 L41178225193.100L41178225193.99 L44894663667.88 L47425069837.94 L47427560098.93 L51133765243.94 L51135469524.93 L5744891568.104 L5745094272.98  L58014502560.99 L59308579027.101L59308843489.98 L59308906961.104L59310683405.94 L60093563309.85 L60095729573.84 L61929571768.83 L6312402539.96  L6314191681.98  L63368150556.99 L63374621462.100L68384130463.10000000=00J00^01401D01P01\02302A02f03;03O03a04304L04U04^04g05005E05m06;06V07?07Y07m08:08G08[08n09Q09\09g0:5S3hAR1U1n3U68S3hAR1U1n3U68S3hAR1U1n3U682N03UCES3hAR1v2mh1U1n2EB4EBLES3hAR1U1n1c1H2H0S3hAR1U1n2N0S3hAR1U1n2N0S3hAR1U1n1x2P12P22Q12Q2S3hAR1U1n1x2HxS3hAR1v1U1n4STK04STK21c1Y2AL3IMH4IMG2S3hAR1U1n1c1t1R2T02T2S3hAR1U1n2cc3CC13CC2S3hAR1U1n3ACB1t2APS3hAR1U1n3ACB1t2APS3hAR2AL1U1n3IMH3U681e2H0S3hAR1U1nS3hAR1U1nS3hAR1U1nS3hAR1U1nS3hAR1U1n1x1t1R2T02T2S3hAR1v1U1n4STK04STK21x1Y2AL3IMH4IMG22IMS3hAR1U1n1c2CBS3hAR1U1n3UHI3ACB1c2XB2CB1HS3hAR1v1U1n4STK03UCE1x1Y2XB2AL3IMH3U682IMS3hAR1U1n1t3APT3ACB1x1R2XBS3hAR1U1n3CLM2N03ACBS3hAR1U1n3UCES3hAR1U1n3UCES3hAR1U1n3U682N03UCES3hAR1U1n1H3HU23HU1S3hAR1U1n3HU03HU13HU23ACB1H2M12M21XS3hAR1U1n1cS3hAR1U1n1cS3hAR1U1n1c2CB". (* [comment removed for export] *)
#[using="Type"] Theorem HKv_rereserve : ltac2:(CDefT.buildp (gd_tbl_AVm ()) "Pv,$68.Pmh,$6:.PU,$4.Pn,$4.P,(92.R4.R2.R1.R3.)P,(12.$4.(65.VAL,)+7???8000.)P,(2.(3<.VAL,)+65?000.)P,(32.R7.R5.R4.)P,(2.+65?000.R6.)P,(0.(2.(<.R7.R6.)+7???7000.)(2.+10007???8000.R7.))P,Pt,$?.P,(10.$?.R1.(11.R;.))(0.(2.(<.R:.R9.)(16.R2.))(2.(17.R2.)R:.))P,(>.(19.$4.$4.)Lc,(19.$4.$4.)(1.(10.(19.$4.$4.)R1.(43.R<.))(1.(2.(3.$4.$4.R1.)R:.)(2.(<.R:.R9.)(<.(3.$4.$4.R1.)(7.$4.$4.R1.))))))P,(>.(19.$4.$4.)LH,(19.$4.$4.)(1.(10.(19.$4.$4.)R1.(35.R=.))(1.(2.(3.$4.$4.R1.)R;.)(2.(<.R;.R:.)(<.(3.$4.$4.R1.)(7.$4.$4.R1.))))))(1.(12.$13.(6=.(1<.(19.(30.&40.)(30.&40.))(5=.(53.R<.))(5:.(53.R<.)))(76.&40.R;.)(76.&40.R:.))$15.)(6;.R=.(93.R;.R:.R<.)))")
(* [comment removed for export] *).
Proof.
  (intros v mh U n [K (VW & MHv & CLM & CLN & CLL)] ASB IMH HUN U68 UHI APT dd_H; ddestruct dd_H as (cc & Hcc & CC1 & CC2); intros dd_H; ddestruct dd_H as (HU0 & HHU & HU1 & HU2)).
  dpose K as (Hh & ND & GD & LZ & LIM & EB & BUD0 & WF & (TB & TN & TL & THL & TEM & MND & MSEP & NZN & NZL & BANDM) & (CE1 & CE2 & CE3 & CE4) & RS & RC & _ & AT).
  dpose VW as (TWF & APT2 & HWF & HAP & THA & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & GWF & BANDCS & EB0 & TND & UW & USEP & HUL & UT).
  ddestruct TEM as (UNC & MPOS & LZK & MX & MH).
  dpose (UW U n HUN) as (N0 & U0 & UCE & UAL & NAL).
  aceilb.
  assert (UZ : bv_unsigned (Z_to_bv 64 U) = U) by (apply u64_lit; lia).
  assert (NZ : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  assert (RFR : region_free (vm_reserved (m_vmmaps mh) ++ vm_maps (m_vmmaps mh)) (Z_to_bv 64 U) (Z_to_bv 64 n) = true).
  { apply clear_region_free; [lia| lia| lia|]. apply clear_app; [| exact CLM]. intros e He. destruct (RS e He). lia. }
  split; [exact RFR|].
  ddestruct (eager_rereserve_le mh U n WF ltac:(lia) N0 ltac:(lia) UAL NAL) as (WF' & EBLE & PL).
  assert (PMM : vm_maps (m_vmmaps (norep_grant U n mh)) = (Z_to_bv 64 U, Z_to_bv 64 n) :: vm_maps (m_vmmaps mh)).
  { unfold norep_grant. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj. reflexivity. }
  assert (PMN : vm_noaccess (m_vmmaps (norep_grant U n mh)) = (Z_to_bv 64 U, Z_to_bv 64 n) :: vm_noaccess (m_vmmaps mh)).
  { unfold norep_grant. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj. reflexivity. }
  assert (PMR : vm_reserved (m_vmmaps (norep_grant U n mh)) = vm_reserved (m_vmmaps mh)).
  { unfold norep_grant. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj. reflexivity. }
  assert (PML : vm_limit (m_vmmaps (norep_grant U n mh)) = vm_limit (m_vmmaps mh)).
  { unfold norep_grant. cbv zeta. rewrite vmmaps_with_mmap_backing. model_proj. reflexivity. }
  assert (PT : m_vm_materialized (norep_grant U n mh) = m_vm_materialized mh).
  { unfold norep_grant, with_mmap_backing. cbv zeta. destruct (mmap_noreserve_b (Z_to_bv 64 1064994)); model_proj; reflexivity. }
  unfold HKv. rewrite PMM, PMN, PMR, PML, PL, PT.
  split; [rewrite halted_norep_grant; exact Hh|].
  split; [exact ND|].
  split; [exact GD|].
  split.
  { (* [comment removed for export] *)
    intros x AOK PIR. rewrite page_in_ranges_cons in PIR. apply Bool.orb_true_iff in PIR. destruct PIR as [PIR|PIR]; [| exact (LZ x AOK PIR)].
    exfalso. cbn [fst snd] in PIR. rewrite UZ, NZ in PIR. apply andb_prop in PIR. destruct PIR as [P1 P2]. apply Z.leb_le in P1. apply Z.leb_le in P2.
    assert (XB : 0 <= x < 2^64 -> U <= x < U + n).
    { intros XR. ddestruct (page_base_of_facts x XR) as (Q1 & Q2 & Q3). unfold page_size in *. lia. }
    destruct AOK as [CX|[(c & Cc & ->)|IM]].
    - destruct CX as [Y|[(Y & _ & _)|(t & Ht & TC & R)]].
      + specialize (XB ltac:(lia)). lia.
      + rewrite IMG0, IMG1 in Y. specialize (XB ltac:(lia)). lia.
      + pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _). unfold t_hi in *. specialize (XB ltac:(lia)). specialize (APT t Ht). unfold t_hi in APT. lia.
    - assert (CB : 0 <= c < 2^47).
      { destruct Cc as [Y|[(Y & _ & _)|(t & Ht & TC & R)]]; [lia| rewrite IMG0, IMG1 in Y; lia|].
        pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _). unfold t_hi in *. lia. }
      unfold shadow_of in *. rewrite ASB in *.
      assert (c / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia). pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)).
      specialize (XB ltac:(lia)). lia.
    - specialize (XB ltac:(lia)). lia. }
  split; [exact LIM|].
  split; [cbn [v_eb v_hole] in EB; lia|].
  split; [exact BUD0|].
  split; [exact WF'|].
  split.
  { (* [comment removed for export] *)
    split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]].
    - apply Forall_forall. intros t Ht. pose proof (proj1 (Forall_forall _ _) TB t Ht) as (F1 & F2 & F3).
      pose proof (APT t Ht) as AP. unfold tfacts. unfold t_hi in *.
      split; [apply covers_cons; exact F1|]. split; [intros HLt; apply haslit_cons; exact (F2 HLt)|].
      destruct (t_kind t).
      + destruct F3 as [G1 G2]. split; (apply clear_cons; [assumption| rewrite UZ, NZ; lia]).
      + apply clear_cons; [assumption| rewrite UZ, NZ; lia].
      + exact I.
    - intros e [<-|He]; [cbn [fst snd]; rewrite UZ, NZ; apply covers_cons_new; rewrite ?UZ, ?NZ; lia| apply covers_cons; exact (TN e He)].
    - intros e [<-|He]; [cbn [fst snd]; rewrite UZ, NZ; apply covers_cons_new; rewrite ?UZ, ?NZ; lia| apply covers_cons; exact (TL e He)].
    - intros U9 n9 HU9. destruct (Z.eq_dec U9 U) as [EU|NU]; [destruct (Z.eq_dec n9 n) as [EN|NN]|].
      + subst. apply covers_cons_new; rewrite ?UZ, ?NZ; lia.
      + apply covers_cons. apply (THL U9 n9). split; [exact HU9| intros [_ E]; exact (NN E)].
      + apply covers_cons. apply (THL U9 n9). split; [exact HU9| intros [E _]; exact (NU E)].
    - split; [| split].
      + intros U9 n9 HU9 APU x Hx. destruct (Z.eq_dec U9 U) as [EU|NU]; [destruct (Z.eq_dec n9 n) as [EN|NN]|].
        * subst. exists (Z_to_bv 64 U, Z_to_bv 64 n). split; [left; reflexivity| cbn [fst snd]; rewrite UZ, NZ; lia].
        * ddestruct (UNC U9 n9 (conj HU9 (fun E => NN (proj2 E))) APU x Hx) as (e & He & E). exists e. split; [right; exact He| exact E].
        * ddestruct (UNC U9 n9 (conj HU9 (fun E => NU (proj1 E))) APU x Hx) as (e & He & E). exists e. split; [right; exact He| exact E].
      + intros e [<-|He]; [cbn [snd]; rewrite NZ; lia| exact (MPOS e He)].
      + split; [| split].
        * (* [comment removed for export] *)
          intros e [<-|He] x Hx.
          -- right. dexists U, n. split; [exact HUN|]. cbn [fst snd] in Hx. rewrite UZ, NZ in Hx. exact Hx.
          -- destruct (LZK e He x Hx) as [X|(U9 & n9 & [HU9 _] & RU)]; [left; exact X| right; dexists U9, n9; split; [exact HU9| exact RU]].
        * (* [comment removed for export] *)
          intros e [<-|He] x Hx.
          -- right. dexists U, n. split; [exact HUN|]. cbn [fst snd] in Hx. rewrite UZ, NZ in Hx. exact Hx.
          -- destruct (MX e He x Hx) as [X|(U9 & n9 & [HU9 _] & RU)]; [left; exact X| right; dexists U9, n9; split; [exact HU9| exact RU]].
        * (* [comment removed for export] *)
          intros e H [<-|He] HH M1 M2; [| exact (MHv e H He HH M1 M2)]. cbn [fst snd] in M1, M2 |- *. rewrite UZ, NZ in *.
          destruct (HAP H HU0 HH HHU) as [<-|X]; lia.
    - constructor; [| exact MND]. intros Hin. specialize (CLM _ Hin). cbn [fst snd] in CLM. rewrite UZ, NZ in CLM. lia.
    - apply msep_cons; [exact MSEP| rewrite UZ, NZ; exact CLM].
    - intros e [<-|He]; [cbn [snd]; rewrite NZ; lia| exact (NZN e He)].
    - intros e [<-|He]; [cbn [snd]; rewrite NZ; lia| exact (NZL e He)].
    - ddestruct BANDM as (B1 & B2 & B3). repeat split; apply covers_cons; assumption. }
  split.
  { split; [| exact (conj CE2 (conj CE3 CE4))].
    intros e He R1 R2. apply in_app_iff in He. destruct He as [He|[<-|He]].
    - apply CE1; [apply in_app_iff; left; exact He| exact R1| exact R2].
    - exists cc. split; [exact Hcc|]. cbn [fst snd]. rewrite UZ, NZ. lia.
    - apply CE1; [apply in_app_iff; right; exact He| exact R1| exact R2]. }
  split; [exact RS|]. split; [exact RC|]. split; [exact VW|].
  rewrite alloc_top_norep_grant. exact AT.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End AVm.

End ARUN_1.
