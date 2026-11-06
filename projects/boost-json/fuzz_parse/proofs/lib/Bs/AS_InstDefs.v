(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.boost_json.fuzz_parse.images Require Import AsanUbsan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel SReach LazyRestrict LazyLedger LazySR LazyNodes BothAllocCons BothAllocConsC.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsDriverLaws AsSR AsChain FakeStackRep
     AllocWf AllocKit AllocRep AllocRepFacts AllocRepX SecLazy AsDepotInv AsDepotHash AG_Malloc2 AG_MallocLarge3 AG_MallocAll.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4bool46Stdlib6ZArith6BinInt1Zjb3lebjb3mul79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAsDriverLaws~~~~~~lf9ADRV_LIVElf8ADRV_CNThc4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAS_InstDefs~~~~~~rf3ist79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~hg65blockjb2le37Corelib4Init5Logichl13andhg64aclsjb3addhc6lengthhl12eqhl13not89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAS_InstDefs4Defs~~~~~~hp0dILIVE_CNT_MAXhp09ILIVE_MAXhg66AK_CLShg66acsizehg6bclass_byteshg68lb_bytesjb6of_nathc4prodhc4pair37Corelib5Lists7ListDefija3maphg68blk_addrhg68blk_sizehg64bptrhc4negbhg66blk_idjb3eqb36Stdlib4Bool4Booliof7Is_true25stdpp4baseiqc6filter25stdpp9decidableis2bIs_true_dec35stdppblist_basics4listiu2blist_filter3h5LinuxProcessSemanticsfLinuxProcessSem5Statejg95Model04Nposrf4ip_D35stdpp9bitvectorbdefinitionsjkdbbv_unsignedhc4truejg98m_vmmapsjg97vm_maps69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~jp79kPageSize69OSSVerify6Proofsaboost_jsonafuzz_parse3libcLazyRestrict~~~~~~ju5ain_rangesbjb2ltjkd2bvhp07dtv_covrf3i_drf3i_s79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs9AllocRepX~~~~~~kl47AMODELXkl49depot_cov79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAsDepotInv~~~~~~kqb5depotkqb5d_idsrf5ip_TR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsbAsDepotHash~~~~~~lg5adepot_hashkqb3d_Kkqb8d_frameskqb6d_hash36Stdlib5Lists4Listln12Inln15NoDuphg63mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~lpa4cellhc4conshc3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~lub5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AllocRep~~~~~~mif3ATPlpa2C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~mna8rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~ms12wzmif5akobj79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs8AsShadow~~~~~~ngb5aceiljb6modulomif3astmif4disjjp7h0kPtrArrayReservejp7akSpaceSizemif4a_pamif4a_sbmif5a_thrkqb4d_nbkqb4d_sbjp76astate69OSSVerify6Proofsaboost_jsonafuzz_parse3libdBothAllocCons~~~~~~ns05INITQ69OSSVerify6Proofsaboost_jsonafuzz_parse3libeBothAllocConsC~~~~~~og95PINVcmif5a_fsbmif8AFS_SIZEhl12exjp76schunkrf6ip_fsbmif4a_stija6Foralljp76as_secjp7bkNumClassesjp7asc_map_begjp7bsc_map_sizeog96AK_CAP79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BsaAG_Malloc2~~~~~~ot3cdepot_placedhp04ATHRhp07IDAPARThp05PINVIhp08depot_trhp03lbpmif6ARHEAPmiffashadow_visiblekl48awin_viskl4aflagsx_repkqb5DEPOTjb3powhg63asrmif3a_Lmif3a_Shp03ICfhp03ICmhp02IKhp06IRHEAPhp09Ialloc_okhp0aIlb_removehp09Irauxv_okmif4a_ALmif4a_Zr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsChain~~~~~~qg36achainhg69Build_asr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs4AsSR~~~~~~ql75AKRELql72SRql73VIS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscFakeStackRep~~~~~~qq74RFSI79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7SecLazy~~~~~~qv1anonvm_samerf7iparams" s.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record iparams : Type := IP {
  ip_fsb : Z;                 (* [comment removed for export] *)
  ip_D   : Z;                 (* [comment removed for export] *)
  ip_TR  : list (list Z)      (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Record ist {HCEIL : HeapCeil} : Type := IST { i_s : ast ; i_d : depot }.
Arguments IST {HCEIL} _ _.

Section Defs.
  Context {HCEIL : HeapCeil}.
  Variable p : ltac2:(zQ "10!rjc$0").

  (* [comment removed for export] *)
  Definition ICm : ltac2:(zQ "10!h9>1n$0$0") := ltac2:(zQ "40!j4!h9!l3!l9\1n$1M0\0$0$1@2$2^1+vsg0Z@2$3+4^1").
  Definition ICf : ltac2:(zQ "10!h9>1n$0$0") := ltac2:(zQ "10!h9\1n$0Z").
  Definition ILIVE_MAX : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!q1$0").
  Definition ILIVE_CNT_MAX : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!qd$0").
  (* [comment removed for export] *)
  Definition Ialloc_ok : ltac2:(zQ "40!r8!h9!hg0!hk3>1x@1$2?5HCEIL>2LB@1$0$3>1n$1P") := ltac2:(zQ "h20!hkc!hm5!hmc!hn4!h9!hk3!hna!r8!ho3!ho9!ht6!hu7!hg0!hv4!hve!ig8!ih7!ii3\1x@1$c?5HCEIL\2LB@1$7$5\1n$4@2$1@2$0+1^1@2$1>0@1$9@3$8$4@1$2^1Z@2$0@2$3@2$f^3@1$2^2@1$e@1$2^2$d@2$1@2$0@2$3@1$h1@2$6$5^2+1$a@2$0@2$3@1$h0^2^1$b").

  (* [comment removed for export] *)
  Definition lbp : ltac2:(zQ "40!r8!h9!iic!hk3>2LB@1$0$3@1$0@2$2$1$1") := ltac2:(zQ "80!h9!hk3!r8!ij3!iic!il1!il8!im4\2LB@1$2$1@4$5$1@2$4$0$0\1b$1@4$3$0$0@1$6^1@1$7^1^1").
  Definition Ilb_remove : ltac2:(zQ "30!r8!hk3!in0>1q$2>2LB@1$0$1@1$0$1") := ltac2:(zQ "a0!hk3!r8!in8!inf!io9!in0!iq1!ir8!it3!iva\1q$5\2LB@1$1$0@6$7$0@1$1$0@1$9$0\1b$0@1$6@1$2@2$4@1$3^1^3\1x$0@1$8@1$2@2$4@1$3^1^3^1").

  (* [comment removed for export] *)
  Definition dtv_cov : ltac2:(zQ "10!jj7>2mo$0P") := ltac2:(zQ "h00!jk0!jk6!jma!j4!jn9!hm5!ho3!jj7!jo0!joc!jt8!ki4!hn4!hkc!kj2!kj7\2mo$7>1x@1$f@1$0#k0>0@2$5@2$d@1$1?1p@2$2@1$0#k0^1@2$e@2$2@1$0#k0^1@2$c@1$1?1p$a@3$6$3@2$b^2@1$9@1$8^3$4").
  Definition IK : ltac2:(zQ "20!jj7!hg0>1x@1$1?5HCEIL>2mo$0P") := ltac2:(zQ "80!hm5!jj7!kjd!kk8!kke!hg0!kp3!kpe\1x@1$5?5HCEIL\2mo$1@2$0@3$6?5HCEIL@2$4?5HCEIL^2^1@2$0@2$7@2$3?5HCEIL^2^1@1$2^1").

  (* [comment removed for export] *)
  Definition depot_tr : ltac2:(zQ "10!kub>1d$0P") := ltac2:(zQ "f0!h9!hm5!hkc!kv4!r8!il1!kvd!lk6!ll4!llb!lm7!kub!lo4!loa!l9\1d$b@2$1@2$2+1@1$3^1@2$1>2id$0>0@2$1@2$2+2^1@2$2^1@1$3^2@3$c$0@2$a^3^2@4$5@1$4$0$0$7@1$6?1p@2$1@2$d$0@1$8^1@2$2@1$9^1@2$e+i0@1$3^1").

  (* [comment removed for export] *)
  Definition ATHR : ltac2:(zQ "10!lp3>1m$0P") := ltac2:(zQ "h40!jk6!hm5!lt6!hn4!lte!lu5!mi6!mmd!mn4!mr5!mvc!ho3!h9!jt8!ng2!lp3!nk9!hkc!kj2!nl2\1m$f@2$1@4$9$6^1@2$3$7+8@3$4$2@1$8@1$a@1$0?1p@1$5$2@2$1@4$9$6^1@2$3@1$0?1p+h8@3$4$2@1$8@1$a$7@1$5$2@2$1@2$h2Z@1$0?1p@2$1@3$b$c@2$h3@1$0?1p+8Z@2$1@2$h1@2$3@1$0?1p+i0@1$h0?5HCEIL@3$e?5HCEIL@1$0?1p$d").

  (* [comment removed for export] *)
  Definition IDAPART : ltac2:(zQ "20!nlb!kub>1s$0>1d$1P") := ltac2:(zQ "f0!jt8!jk6!nm2!hm5!l9!nma!nnf!nod!np5!npd!nlb!nq6!nqe!kub!hn4\1s$a\1d$d@2$3@4$2@1$8^2@2$e$6$0@1$1?1p$0@2$3@4$2@1$9^2$0@1$1?1p$0@2$3@4$2@1$7^2$5@1$1?1p$0@2$3@4$2@1$b^1@2$4+h0+hggg0@1$1?1p$0@4$2@1$c^1@2$4+8+ogg0@1$1?1p$0").

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition PINVI : ltac2:(zQ "10!nr6>2st$0P") := ltac2:(zQ "40!hm5!nr6!og0!oka\2st$1@2$0@1$3^1@1$2^1").   (* [comment removed for export] *)

  Definition IRHEAP : ltac2:(zQ "40!r8!hg0!hk3!lp3>1x@1$1?5HCEIL>2LB@1$0$2>1m$3P") := ltac2:(zQ "jf0!hm5!hkc!jk0!ol3!nm2!hk3!kj7!ho3!h9!olc!lt6!lte!om8!jt8!ome!jk6!on8!mi6!oo1!im4!mn4!l9!hna!r8!lu5!oo9!op3!opd!oqc!ora!os9!ph3!pi3!pib!ht6!pj6!pjf!pkb!kk8!kke!hg0!pl2!npd!plc!nlb!pmf!pnb!po9!nq6!nqe!kub!il8!inf!in0!ig8!lp3!mr5!lo4!hn4!kj2!nl2!ii3!pp2\1x@1$i8?5HCEIL\2LB@1$h7$5\1m$j7=1s$ic@2$i7?5HCEIL^3=1d$j2@2$i6?5HCEIL^4@2$0@4$i9?5HCEIL^2@1$i5^4^3@2$0@3$h9$5\1b$5@2$0@3$7$j5@1$j4^1@1$j3^1@2$0@2$1+1@1$h3^1@2$1@1$h3^1@2$je+2+hf^4@2$0@2$1@1$jd@2$h6$5^4$i2@2$0@2$id^2^3@2$0@1$ie^3@2$0@3$if$h1^1^3@2$0@3$hf?5HCEIL^2^1@2$0@1$i4^1@2$0@4$4@1$3^2$9@1$j0^1@2$h5+h0+hggg0@2$0@4$4@1$3^2$9@1$j1^1@2$h5+8+ogg0@2$0@3$7$8@1$3^2@1$h0?1p@2$0@3$7$8@2$jc@1$h0?1p+hgg0Z@2$0@4$4@1$3^2$9@1$f?1p$d@2$0@1$i0^3@2$0@2$c@1$6@1$2#k0\2tb@1$6@1$2#k0@2$c@1$6@1$2#k0\2te@1$6@1$2#k0@4$j8$h1^5@2$ja@1$ia^4+j0@3$b$a@1$h4^2@3$b$a@1$h4^1@1$h8$a@2$0@1$ib^2@2$0@2$i1^2^1@2$0>2sc$e>0@3$j9$e^1@1$ha@1$h2^3@4$4@1$hc^2@1$hd^2@1$f?1p$d@2$0@1$i3@1$h2^2>1c$8>0@2$0@2$1+1^1@2$jb^1$hb@2$1@2$j6^6^2$he").        (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition Irauxv_ok : ltac2:(zQ "20!h9!lp3>1m$1>1B$0P") := ltac2:(zQ "50!h9!lp3!hn4!hkc!pp2\1m$1\1B$0@2$3@2$2^1+h0@2$4+2+if").

  (* [comment removed for export] *)
  Definition KHp : ltac2:(zQ "10!pp8$0") := ltac2:(zQ "h82!hg0!kke!on8!ppf!pq6!pqd!pr4!prb!ht6!hu7!ps1!psb!pt8!pu6!kvd!pv3!pvb!qk0!qka!qp1!qpa!qq0!qu9!rie&\1x@1$0?5HCEIL@1$3@2$1?5HCEIL^1&\1x@1$0?5HCEIL@1$4@2$1?5HCEIL^1@h2$h2@1$0?5HCEIL$h4@3$h5@1$0?5HCEIL~0~1@5$h3@1$0?5HCEIL~0~1\1x@1$0?5HCEIL@1$h0@2$1?5HCEIL^1$7$h7$a@2$h6?5HCEIL@1$2?1p$d$c$b$9$8\1x@1$0?5HCEIL@1$f@2$1?5HCEIL^1$6$5@1$h1?5HCEIL@1$e?1p@1$2?1p").
End Defs.
