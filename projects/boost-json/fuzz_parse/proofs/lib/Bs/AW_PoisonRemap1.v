(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics AsDepotInv F_memset AllocWalkKit.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import AW_Leaves AW_PoisonShadow AW_SysconfPg AllocTacX.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~0ddisjoint_from37Corelib7Numbers7BinNumskb4Npos35stdpp9bitvectorbdefinitionsmb2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsfAW_PoisonRemap1~~~~~~od4RENV37Corelib4Init9Datatypest94listt96option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hg15asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~hk53mem03ivl05munch05wmono" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Record RENV (g : word) (b244 : byte) (m : mem) : Prop := mkRENV {
  re_got  : rw_cells asegs m 1778520 (map (fun v => C8 (wz v)) AGOT_VALS);                       (* [comment removed for export] *)
  re_shb  : rw_cells asegs m 1823096 [C8 (wz 2147450880)];                                      (* [comment removed for export] *)
  re_hme  : rw_cells asegs m 1826400 [C8 (wz 140737488355327); C8 (wz 0); C8 (wz 0)];           (* [comment removed for export] *)
  re_thresh : rw_cells asegs m 2420000 [C8 (wz 0xffffffffffffffff)];                                       (* [comment removed for export] *)
  re_mlim : rw_cells asegs m 2420024 [C8 (wz 0)];                                               (* [comment removed for export] *)
  re_dd   : rw_cells asegs m 2420099 [C1 (b8 1)];                                               (* [comment removed for export] *)
  re_madv : rw_cells asegs m 2420124 [C1 b244];                                                 (* [comment removed for export] *)
  re_rms  : rw_cells asegs m 1786752 [C8 (wz 1714080)];                                         (* [comment removed for export] *)
  re_psc  : rw_cells asegs m 2411552 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_lpg  : rw_cells asegs m 7411160 [C8 (wz 4096)];                                            (* [comment removed for export] *)
  re_ssp  : rw_cells asegs m 1782024 [C8 (wz 7410520)];                                         (* [comment removed for export] *)
  re_grd  : rw_cells asegs m 7410520 [C8 g]                                                     (* [comment removed for export] *)
}.

End HCW.

(* [comment removed for export] *)

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma renv_transport : ltac2:(zQ "b0!jc!m4!o8!t2!v1!v8!hjc!ho3!hoa!hof!hp6>1g@1$2@1$1#k0>1b@1$2@1$1#8>1m$7>2m'>0@1$2@1$1#k0@1$5@1$2@1$1#8>1W@1$4$8>0@3$3^5^4^3>0@3$9^2^4^3>0@3$a$6^5^4>0@3$0^4+hrijl8+n8>0@3$0^5+hrthn8+8>0@3$0^6+hrtum0+h8>0@3$0^7+ikuti0+8>0@3$0^8+ikutj8+8>0@3$0^9+ikuto3+1>0@3$0^a+ikutpc+1>0@3$0^b+hrkjo0+8>0@3$0^c+ikssi0+8>0@3$0^d+nhhlt8+8>0@3$0^e+hrjhg8+8>0@3$0^f+nhhjl8+8@3$3^h4^h3^h1").
Proof.
  intros g b m m' W E MU WM; intros; destruct E; constructor;
    (eapply rw_cells_transport; [eassumption | exact MU | exact WM | ]);
    unfold AGOT_VALS; cbn [cells_size csize length map Nat.add Nat.mul]; assumption.
Qed.

End HCW2.

Ltac renv_at E MU WM E' :=
  lazymatch type of MU with munch ?W ?m ?m' =>
    lazymatch type of E with RENV ?g ?b m =>
      region_table; region_hull_memo W;   (* [comment removed for export] *)
      assert (E' : RENV g b m');
      [ apply (renv_transport g b m m' W E MU WM); cbn [disjoint_from]; region_decide | ]
    end end.

(* [comment removed for export] *)
Section HCW3.
  Context {HCEIL : HeapCeil}.

(* [comment removed for export] *)

End HCW3.
(* [comment removed for export] *)
