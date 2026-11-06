(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prodhc4conshc4pairhc3nil04Npos35stdpp9bitvectorbdefinitionslc2bvlc7Z_to_bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~o86mstateo84optr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~t62wzo85oconco84meta46Stdlib6ZArith6BinInt1Zhic3addhic3mulo8am_freeableo8am_last_idxo88m_mapleno8bm_sizeclass79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ho54cellho52C8t62pwho52C4t69meta_wordo87m_availo87m_freedo85m_memo86m_nexto86m_prev01No88brkstateo85c_brko84conco83ctxhic3powhic3subo8cc_avail_metao8h7c_avail_meta_area_counto8h2c_avail_meta_areaso8h2c_avail_meta_counto8h0c_free_meta_heado8bc_init_doneo8h2c_meta_alloc_shifto8h0c_meta_area_heado8h0c_meta_area_tailo8ec_mmap_countero88c_secreto84mctxhc3nat37Corelib5Lists7ListDefji43mapji43seqo86activehic6of_nato85usaget62b8o89unmap_seqo87bouncesji46repeatt68brk_wordt65zerosho52C1ho52CBo85c_seqo86regiono86r_baseo85rkindo86r_kindt65lr_lohic2le37Corelib4Init5Logicju12eqo87RKGroup79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_syscalls~~~~~~kg55asegst63CTXju13and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~kle6u64arrkle5u8arr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~kqb8rw_cellst67activest68bouncesst6ectx_head_cellst6ectx_tail_cellst6aunmap_seqst66usagest65MLOCKt6aNEED_LOCKSt6bPAGE_SIZE_Ao84aptro84areao88AREA_HDRo89META_SIZEt6ameta_cellso86NSLOTSo87a_checko86a_nexto88a_nslotso84aaddo8cget_meta_rechic2lt35stdpp7numbers1Nlt76eq_dec35stdpp7numbers1Zlv26eq_dec25stdpp9countablemgdbN_countablemgdbZ_countablemgdeprod_countable25stdpp9decidablemkebprod_eq_dechc4Somehc6option89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep4MREP~~~~~~mne8area_repo87s_areas25stdpp4basemtb6lookup25stdpp4gmapmv14gmapmv1bgmap_lookupo84ghdrju12exo8cg_active_idxo86g_metahic4landlcbbv_unsignedmne9group_repo88s_groupso85r_leno8bround_up_pg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~nnd8bytes_atnnd5wr_ato85Knowno89cell_reado87cellvalo8aget_shadowmneashadow_repo89s_regionshc3sndhic6modulohc3fstju13nott6eagent_reservedhc4boolhc4trueju12oro8dalloc_ceilingo8branges_freeo8as_reservedmneamrep_areasmne8mrep_ctxmnecmrep_globalsmnebmrep_groupsmnebmrep_shadowmnearegions_wfmtb7is_Somennd3zxbnnd4zx16nnd4sx32hic5ldifflc8bv_swraplc9bv_signedo8asize_classnnd3le2o86shadowo88s_shadowo86s_tick46Stdlib6NArith6BinNat1Npk72leo85r_havo86r_havp36Stdlib5Lists4Listpn62Inmtb6insert25stdpp8fin_mapspp9amap_insertmv1h2gmap_partial_altero88mkShadowo87r_cellso83wr8hc2ido87shadow025stdpp6optionpv8bfrom_optiont68ticks_okhic3divo88aptr_eqbo88upd_metao8aset_activehic3eqbkle3updhic6to_natt69shadow_lehc5falseo85staleo87hav_addt68sh_tickso8bhavoc_unitso8bhavoc_pageso88set_tick" s.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition CTX : Z := 0x1a0b8.
Definition MLOCK : Z := 0x1a000.
Definition LIBC : Z := 0x1a050.
Definition NEED_LOCKS : Z := 0x1a053.     (* [comment removed for export] *)
Definition PAGE_SIZE_A : Z := 0x1a080.    (* [comment removed for export] *)
Definition SIZE_CLASSES : Z := 0x180a0.

     (* [comment removed for export] *)
       (* [comment removed for export] *)
Definition alloc_meta_entry : Z := 0x15f04.
Definition alloc_slot_entry : Z := 0x16210.

(* [comment removed for export] *)
Definition agent_reserved : ltac2:(zQ "30!h9!j4!jb@1$1@2$2$0$0") := ltac2:(zQ "50!h9!jb!k2!k9!l0@3$2@2$1$0$0@4$3$0$0+hggg0+pgg0@3$2@2$1$0$0@4$3$0$0+hpgg0+igg0@1$4@2$1$0$0").

Definition wz : ltac2:(zQ "30!l6!h9!n9>1z$1@1$2@1$0#k0") := ltac2:(zQ "30!l6!h9!ne\1z$1@2$2@1$0#k0^1").
Definition b8 : ltac2:(zQ "30!l6!h9!n9>1z$1@1$2@1$0#8") := ltac2:(zQ "30!l6!h9!ne\1z$1@2$2@1$0#8^1").
(* [comment removed for export] *)
Definition pw : ltac2:(zQ "40!l6!s6!sf!n9>2st$1>1p$2@1$3@1$0#k0") := ltac2:(zQ "40!hh8!s6!hhd!sf\2st$1\1p$3@1$0@2$2^2^1").

(* [comment removed for export] *)
Definition meta_word : ltac2:(zQ "20!h9!hi5>2mr$1$0") := ltac2:(zQ "70!hk4!hkb!hl2!hlf!hmc!hn7!hi5\2mr$6@2$0@2$0@2$0@1$3^1@2$1+i0@1$2^1@2$1+k0@1$5^1@2$1+hgg0@1$4^1").

Definition meta_cells : ltac2:(zQ "40!j4!hs1!hi5!s6>2st$3>2mr$2@1$0$1") := ltac2:(zQ "f0!hs1!k2!hs9!hsf!hh8!ht4!l0!hta!hu6!hv0!hva!ig2!igb!hi5!s6\2st$e\2mr$d@3$1$0@1$2@2$3^2@1$c^1@3$1$0@1$2@2$3^2@1$b^1@3$1$0@1$2@2$3^2@1$a^1@3$1$0@1$5@1$4@1$8^1@3$1$0@1$5@1$4@1$9^1@3$1$0@1$2@1$4@1$7^1@1$6$0").

Definition brk_word : ltac2:(zQ "20!h9!s6>2st$1$0") := ltac2:(zQ "a0!h9!ih4!ih7!k9!ii2!iia!ij1!s6!ij7!ije\2st$7M2\1x$2$0@1$4@1$6^1Z@2$9@2$8+2+k0+1\3rid$1\3off$0@2$5^3@4$3$1$0^2^1").

Definition ctx_head_cells : ltac2:(zQ "30!j4!hs1!s6>2st$2@1$0$1") := ltac2:(zQ "h50!hs1!k2!hs9!hh8!hsf!ht4!l0!ik5!il4!imf!io5!ipb!iqf!ird!it3!iu7!ivb!jgc!ij1!jh7!s6\2st$h4=1c$h3@1$h2^1@3$1$0@1$2@1$3@1$h1^1@3$1$0@1$5@1$3@1$c^1@3$1$0@1$5@1$3@1$h0^1@3$1$0@1$2@2$4^2@1$b^1@3$1$0@1$2@2$4^2@1$7^1@3$1$0@1$2@1$3@1$a^1@3$1$0@1$2@1$3@1$8^1@3$1$0@1$2@1$3@1$d^1@3$1$0@1$2@2$4^2@1$e^1@3$1$0@1$2@2$4^2@1$f^1@3$1$0@1$2@2$4^2@1$9^1@1$6$0").

Definition actives : ltac2:(zQ "40!j4!l6!s6!n9>2st$2@1$0@1$3@1$1#k0") := ltac2:(zQ "90!jhe!jjb!jk2!l6!hsf!jk9!s6!jl2!n9\2st$6@4$1$0@1$8@1$3#k0\1i$0@2$4^2@2$5^2@1$7^1@2$2N0Nj0").
Definition usages : ltac2:(zQ "40!j4!l6!s6!n9>2st$2@1$0@1$3@1$1#k0") := ltac2:(zQ "90!jhe!jjb!jk2!l6!hh8!s6!jlc!jl2!n9\2st$5@4$1$0@1$8@1$3#k0\1i$0@1$4@2$6^2@1$7^1@2$2N0Nj0").
Definition unmap_seqs : ltac2:(zQ "40!j4!l6!s6!n9>2st$2@1$0@1$3@1$1#8") := ltac2:(zQ "90!jhe!jjb!jk2!l6!jm4!s6!jm9!jl2!n9\2st$5@4$1$0@1$8@1$3#8\1i$0@1$4@2$6^2@1$7^1@2$2N0Ni0").
Definition bouncess : ltac2:(zQ "40!j4!l6!s6!n9>2st$2@1$0@1$3@1$1#8") := ltac2:(zQ "90!jhe!jjb!jk2!l6!jm4!jn5!s6!jl2!n9\2st$6@4$1$0@1$8@1$3#8\1i$0@1$4@2$5^2@1$7^1@2$2N0Ni0").
Definition zeros : ltac2:(zQ "40!j4!jhe!l6!n9>1n$1@1$0@1$3@1$2#8") := ltac2:(zQ "50!jhe!jnf!l6!jm4!n9\1n$0@3$1@1$4@1$2#8@1$3Z^1").
Definition ctx_tail_cells : ltac2:(zQ "30!j4!hs1!s6>2st$2@1$0$1") := ltac2:(zQ "d0!hs1!k2!l0!jm4!jo9!hh8!jp4!jpc!hs9!jq2!jq8!ij1!s6\2st$c@3$1$0@1$7@1$3@1$a@1$b^1@3$1$0@2$9N7@1$6N7@3$1$0@1$8@1$5@1$4^1@1$2$0").

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lr_lo : ltac2:(zQ "20!h9!jr0>1r$1$0") := ltac2:(zQ "60!jr9!js2!h9!jsa!jr0!hk4\1r$4M1\1x$1$2@1$3^1@2$5@1$0^1+hgg0@1$0^1@1$0^1").

Lemma lr_lo_ge : ltac2:(zQ "40!jt3!jr9!jr0!jtb>1r$2@2$3@1$1^1@1$0^1").
Proof. intros r. unfold lr_lo. destruct (r_kind r); lia. Qed.
Lemma lr_lo_group : ltac2:(zQ "80!jv5!h9!jt3!jvb!jr9!jsa!jr0!js2>1r$6>0@3$0$7@1$5^1$3@3$0$1@1$2^2@1$4^2").
Proof. intros r. unfold lr_lo. intros ->. reflexivity. Qed.

Section MREP.
Variable st : ltac2:(zQ "10!s6$0").
Variable m : ltac2:(zQ "30!l6!n9!mn5>0@1$1@1$0#k0@1$2@1$1@1$0#8").

Definition mrep_ctx : ltac2:(zQ "00P") := ltac2:(zQ "d0!kk8!kl1!kl7!hk4!kp8!kq2!ku6!kv2!kvc!lg7!lh8!li9!lj6@2$2@4$6$0?1m$1@1$9?2st@2$2@4$4$0?1m@2$3$1+l0@1$7?2st@2$2@4$4$0?1m@2$3$1+ht0@1$c?2st@2$2@4$5$0?1m@2$3$1+jl0@1$b?2st@2$2@4$5$0?1m@2$3$1+jn0@1$8?2st@4$6$0?1m@2$3$1+jp0@1$a?2st").

Definition mrep_globals : ltac2:(zQ "00P") := ltac2:(zQ "e0!hs1!k2!l0!kk8!ku6!kl7!hh8!ljf!lk7!ll4!jm4!jpc!ht4!hs9@2$5@4$4$3?1m$7@3$1$0@1$c@1$6Z@1$2$0@2$5@4$4$3?1m$8@3$1$0@1$b@1$aZ@1$2$0@4$4$3?1m$9@3$1$0@1$d@1$6+hgg0@1$2$0").

(* [comment removed for export] *)
Definition area_rep : ltac2:(zQ "20!lm2!lm9>1a$0>2ar$1P") := ltac2:(zQ "hd0!hs1!k2!hk4!kl7!kk8!hh8!ku6!iia!l0!ht4!hs9!ln0!lnb!hkb!h9!lo7!hsf!jp4!jq2!lp4!lpd!lq7!lr0!lrb!lm2!lm9!ls2!jtb!lt1\1a$h8\2ar$h9@2$3@4$6$4?1m@2$7?2st^2@3$1$0@1$a@1$5@1$h4^1@3$1$0@1$a@2$h0?2st@1$h5^1@3$1$0@1$9@1$5@1$h6^1@3$1$0@1$9@1$5Z@1$8$0@2$3>1k$e>0@2$3@2$hbZ^1@2$hc^1$h3@4$6$4?1m@2$2@2$2@2$7?2st^4$b@2$d$c^2@2$f?2st@2$ha?2st@2$h7^4@2$2$b@2$d$c^2@4$6$4?1m@2$2@2$7?2st^2+vu0@3$1$0@2$h2Ni0@1$h1Ni0@1$8$0").
Definition mrep_areas : ltac2:(zQ "00P") := ltac2:(zQ "h20!lm9!ih4!h9!lm2!lu8!mg3!mhe!mid!mjc!mlf!mme!mn5!jv5!ms5!mt1!mu7!mvd!ng5>1a$3>2ar$0>0@3$c@1$b$0@6$f$3$0@4$h0$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0@4$h1$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0^2@1$e?2st@2$a$0^1@2$d^3^2").

(* [comment removed for export] *)
Definition group_rep : ltac2:(zQ "20!lm2!nh4>1b$0>2gh$1P") := ltac2:(zQ "h50!l6!hs1!k2!n9!l0!kl7!jv5!nhb!h9!kk8!hsf!jpc!hs9!ku6!lm2!iia!ni1!nj0!nh4!nj9!nk1\1b$e\2gh$h2@2$7@1$3@1$0#8\2w8@1$3@1$0#8@2$5@4$d$9?1m@2$f?2st^3@3$2$1@1$c@2$a?2st@1$h1^2@3$2$1@1$b^1@1$4$1@3$6$8@2$h3@2$h4@1$0#8^1+hf@1$h0^2").
Definition mrep_groups : ltac2:(zQ "00P") := ltac2:(zQ "h20!nh4!ih4!h9!lm2!lu8!mg3!mhe!mid!mjc!mlf!mme!mn5!jv5!nkf!nlc!mu7!mvd!ng5>1b$3>2gh$0>0@3$c@1$b$0@6$f$3$0@4$h0$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0@4$h1$3@4$9$1$4$2$5@6$8$1$4$6$2$5$7$0^2@1$e?2st@2$a$0^1@2$d^3^2").

(* [comment removed for export] *)
Definition shadow_rep : ltac2:(zQ "20!ih4!jr0>3rid$0>1r$1P") := ltac2:(zQ "h70!kl7!l6!h9!kk8!jr9!nm7!nmf!jtb!lt1!n9!k2!l0!jv5!ih4!jm4!nr7!ns3!nsc!nt4!nu0!nua!jr0!hk4\3rid$d\1r$h5@2$0@4$h0$3?1m@1$4^1@1$6@1$5^1>1o$2>1v$2>0@2$0@2$7Z^2@2$8^2@1$6@1$5^3>0@3$c$h3@2$h2@2$h4?2st^5^3@1$h1^2@2$0@4$f$3?1m@2$h6@1$4^5^4@3$a@1$9@1$1#8@1$e^3@1$b@1$9@1$1#8@2$0@2$7Z^3@2$8^3+hg0").
Definition mrep_shadow : ltac2:(zQ "00P") := ltac2:(zQ "f0!jr0!ih4!jv5!mhe!lu8!mme!mn5!nv7!jvb!jsa!js2!og5!mu7!mvd!ng5>3rid$1>1r$0>0@3$2@1$6$0@6$c$1$0@4$d$1$4$3$0@4$e$1$4$3$0^2@1$b?2st@2$5$0^1>0@3$2$a@1$9^2$8@2$7^4^3").

(* [comment removed for export] *)
Definition regions_wf : ltac2:(zQ "00P") := ltac2:(zQ "ie2!ih4!jr0!h9!lu8!kl7!jv5!mhe!jtb!mg3!mme!mn5!oh1!jr9!nm7!mu7!mvd!ng5!lm9!nh4!nmf!hk4!jb!og5!lm2!mid!mjc!mlf!jt3!oh7!oi1!nhb!oi7!oie!jvb!jsa!js2!ojf!j4!ok6!okd!ol3!om3!mt1!nlc!on1!lt1&@6$e$0$1@4$f$0$3$6$1@4$h0$0$3$6$1@3$hd$0$2^4@1$h6?2st&@3$5@1$a$1~0@2$9$1^1@2$4@3$5@1$i5@2$h5$2$2@1$ic?2st$i0@2$4>3rid$0>1r$1>0@3$5@1$a$1@6$e$0$1@4$f$0$3$6$1@4$h0$0$3$6$1^2@1$h6?2st@2$9$1^1@2$4@2$idZ@1$c^2@2$4@3$5$2@2$hc@1$c^2+hgg0Z@2$4@2$7Z@1$d^2@2$4@2$7@2$h4@1$c^2@1$h3@1$d^2$i8@3$5$i4@3$i9$i0@1$c^2@1$h3@1$d^2$i6@2$4>4rid1$0>2r1$1>4rid2$0>2r2$1>0@3$5@1$a$1@6$e$0$1@4$f$0$3$6$1@4$h0$0$3$6$1^4@1$h6?2st@2$9$1^3>0@3$5@1$a$1@6$e$0$1@4$f$0$3$6$1@4$h0$0$3$6$1^3@1$h6?2st@2$9$1^2>0@1$hf@3$5$0^6^4@2$i7@2$7@2$h4@1$c^6@1$h3@1$d^6@1$hb^4@2$7@2$h4@1$c^4@1$h3@1$d^4@1$hb^6@2$4>1a@2$h5$0$2>2ar$h1>0@3$5@1$a$h1@6$e@2$h5$0$2$h1@4$f$h7@4$ha$0$3$2$8@6$h9$0$3$6$2$8$h8$h1@4$h0$h7@4$ha$0$3$2$8@6$h9$0$3$6$2$8$h8$h1^2@1$ia?2st@2$9$h1^1@2$he$1\1r$1@2$4~1@2$4@2$7Z@3$b$0$2^4@2$4@2$7@2$h4@3$b$0$2^4+hgg0@1$h3@1$d^1@2$4@3$5$2@2$hc@3$b$0$2^4+hgg0Z@2$4@1$hf@3$5$i3@1$i2^1$i1@2$7@1$hb^1@2$h4@1$c^1@3$b$0$2^4>1b@2$h5$0$2>2gh$h2>0@3$5@1$a$h2@6$e@2$h5$0$2$h2@4$f$h7@4$ha$0$3$2$8@6$h9$0$3$6$2$8$h8$h2@4$h0$h7@4$ha$0$3$2$8@6$h9$0$3$6$2$8$h8$h2^2@1$ib?2st@2$9$h2^1@2$he$1\1r$1@2$4~1@2$4@3$5$i3@1$i2^1$i1@2$4@2$7Z@3$b$0$2^4@2$4@2$7@2$h4@3$b$0$2^4+h0@1$h3@1$d^1@3$5$2@2$hc@3$b$0$2^4+h0Z").

Definition mrep : ltac2:(zQ "00P") := ltac2:(zQ "70!kl7!one!ooc!op8!oq8!or7!os6@2$0$6@2$0$2@2$0$3@2$0$1@2$0$4$5").

End MREP.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_aadd : ltac2:(zQ "h10!ih4!h9!jr0!iia!mhe!lu8!oi1!jb!jv5!lrb!s6!og5!hk4!ot4!mu7!mvd!ng5>2st$a>1p@2$7$0$1>1d$1>0@2$d$2@6$e$0$2@4$f$0$5$4$2@4$h0$0$5$4$2@3$6$0$1^2@1$b^3@3$8$1@2$3^4@2$9^3^2@2$c@2$3^4^3^2").
Proof.
  intros st [rid off] d [r Hr]. unfold conc, aadd, get_region. cbn. rewrite Hr. lia.
Qed.

Lemma conc_region : ltac2:(zQ "h10!jr0!ih4!h9!jv5!mhe!lu8!mme!mn5!k9!iia!s6!jr9!og5!hk4!mu7!mvd!ng5>2st$a>3rid$1>3off$2>1r$0>0@3$3@1$7$0@6$e$1$0@4$f$1$5$4$0@4$h0$1$5$4$0^3@1$c^4@2$6$0^1@3$3$2@2$9^5@4$8$1$2^4^3@2$d@1$b^2^3").
Proof. intros. unfold conc, get_region. cbn. rewrite H. reflexivity. Qed.

Lemma round_up_pg_ge : ltac2:(zQ "30!h9!nmf!jtb>1x$0@2$2^1@1$1^1").
Proof. intros. unfold round_up_pg, PGSZ. assert (0 <= Z.land (-x) (4096 - 1)) by (apply Z.land_nonneg; right; lia). lia. Qed.

(* [comment removed for export] *)
Lemma wz_unsigned : ltac2:(zQ "90!h9!kl7!jv5!l6!hh8!jtb!lt1!ij7!nk1>1x$0>0@2$1@2$5Z^1@2$6^1@2$7+2+k0@3$2$0@2$8@1$3#k0@1$4^2^2").
Proof. intros x. intros. unfold wz. apply unsigned_lit. lia. Qed.
Lemma b8_unsigned : ltac2:(zQ "80!h9!kl7!jv5!l6!jm4!jtb!lt1!nk1>1x$0>0@2$1@2$5Z^1@2$6^1+hg0@3$2$0@2$7@1$3#8@1$4^2^2").
Proof. intros x. intros. unfold b8. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. cbn. apply Z.mod_small. lia. Qed.
Lemma zxb_b8 : ltac2:(zQ "a0!kl7!jv5!l6!h9!jm4!hh8!otf!jtb!lt1!n9>1x$3>0@2$0@2$7Z^1@2$8^1+hg0@3$1@1$9@1$2#k0@1$6@1$4^2@1$5^2").
Proof. intros x. intros. unfold zxb, wz. rewrite b8_unsigned by lia. reflexivity. Qed.
Lemma zx16_wz : ltac2:(zQ "90!hh8!kl7!jv5!l6!h9!ou6!jtb!lt1!n9>1x$4>0@2$1@2$6Z^1@2$7^1+hggg0@3$2@1$8@1$3#k0@1$5@1$0^2@1$0^2").
Proof. intros x. intros. unfold zx16, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.
Lemma sx32_wz : ltac2:(zQ "a0!hh8!kl7!jv5!l6!h9!oue!jtb!lt1!ij7!n9>1x$4>0@2$1@2$6Z^1@2$7^1@2$8+2+hf@3$2@1$9@1$3#k0@1$5@1$0^2@1$0^2").
Proof. intros x. intros. unfold sx32, wz. rewrite unsigned_lit by lia. rewrite swrap32_small by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma land_ldiff_distr : ltac2:(zQ "40!h9!nj9!ov6!jv5>1x$0>1a$0>1b$0@3$3$0@2$1^3@2$2^2^1@2$2@2$1^3^2^1").
Proof. intros x a b. apply Z.bits_inj'. intros n Hn. rewrite Z.land_spec, !Z.ldiff_spec, Z.land_spec. destruct (Z.testbit x n), (Z.testbit a n), (Z.testbit b n); reflexivity. Qed.

Lemma land_pgmask : ltac2:(zQ "90!h9!kl7!jv5!nj9!jtb!lt1!oh7!ij7!ije>1x$0>0@2$1@2$4Z^1@2$5^1@2$7+2+k0@3$2$0@2$3^2+vvvvvvvvvvvvvgg0@2$8^2@2$6^2+hgg0").
Proof. intros x.
  intros Hx.
  assert (E : 18446744073709547520 = Z.ldiff (Z.ones 64) (Z.ones 12)) by reflexivity. rewrite E.
  rewrite land_ldiff_distr. rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
  rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  change (2^12) with 4096. pose proof (Z.div_mod x 4096). lia.
Qed.

(* [comment removed for export] *)
Lemma mod_mod_pow2 : ltac2:(zQ "60!h9!oh7!ij7!jtb!kl7!jv5>1z$0>1a$0>1b$0>0@2$4@2$3Z^2@2$3^2^1@3$5$0@2$1@2$1^4@2$2+2^2@2$2+2^3@2$1^4@2$2+2^3").
Proof. intros z a b. intros. apply Z.mod_mod_divide. exists (2^(b-a)). rewrite <- Z.pow_add_r by lia. f_equal. lia. Qed.

Lemma swrap32_mod32 : ltac2:(zQ "60!h9!oh7!ij7!jv5!l6!ovf>1z$0@3$3$0@2$1@2$5@1$4#i0^1@2$2+2+i0@2$1^1@2$2+2+i0").
Proof. intros z.
  unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32) with (2^32). change (2^32 `div` 2) with (2^31).
  rewrite Zminus_mod, Z.mod_mod by lia. rewrite <- Zminus_mod.
  replace (z + 2^31 - 2^31) with z by lia. reflexivity.
Qed.

Lemma signed_wz_small : ltac2:(zQ "90!l6!h9!kl7!jv5!jtb!lt1!ij7!ne!pga>1x$1>0@2$2@2$4Z^1@2$5^1@2$6+2+jf@3$3$1@2$8@1$0#k0@2$7@1$0#k0^2^2").
Proof. intros x.
  intros. rewrite Z_to_bv_signed. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus.
  change (2 ^ Z.of_N 64 / 2)%Z with (2^63)%Z. lia.
Qed.

Ltac nrm := rewrite ?zxb_b8, ?zx16_wz, ?b8_unsigned, ?wz_unsigned by lia.
Ltac st1 := step; try nrm.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma size_class_range : ltac2:(zQ "50!jtb!kl7!ph6!h9!lt1>2sc$3>0@2$1@2$0Z^1@2$4^1+j0@2$1@2$0+1@1$2^2@2$0@1$2^2+hvvf").
Proof. intros sc.
  intros H. unfold size_class.
  assert (F : Forall (fun x => 1 <= x <= 8191) size_classes).
  { unfold size_classes. repeat (constructor; [lia|]). constructor. }
  apply (Forall_nth (fun x => 1 <= x <= 8191) size_classes); [exact F|]. cbn. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma conc_region' : ltac2:(zQ "h30!jr0!ih4!h9!jv5!mhe!lu8!mme!oi1!mn5!oh1!lm2!iia!s6!jr9!og5!hk4!mu7!mvd!ng5>2st$c>1q$a>1r$0>0@3$3@1$8$0@6$h0$1$0@4$h1$1$5$4$0@4$h2$1$5$4$0@3$7$1$2^2@1$e^3@2$6$0^1@3$3$2@2$b^4^3@2$f@1$d^2@3$9$1$2^3").
Proof. intros st [rid off] r H. apply conc_region. exact H. Qed.

(* [comment removed for export] *)
Definition meta_slot : ltac2:(zQ "20!lm2!s6>2st$1>1g$0P") := ltac2:(zQ "hc0!lm2!lm9!h9!ih4!lu8!mg3!kl7!nhb!jv5!mhe!mid!mjc!mlf!mme!mn5!ln0!lnb!lp4!lrb!s6!mt1!hk4!jtb!lt1!hkb!mu7!mvd!ng5\2st$h3\1g$0@2$7$0\1a$0@2$7$1\2ar$1@2$7$2\1k$2@2$6@3$8@1$e$1@6$h9$0$1@4$ha$0@4$c$3$4$2$5@6$b$3$4$9$2$5$a$1@4$hb$0@4$c$3$4$2$5@6$b$3$4$9$2$5$a$1^3@1$h4^5@2$d$1^2@2$6@2$6@2$h6Z^1@2$h7^1$h1@3$8$0^4@2$h2^3@2$h5$f@2$h8$h0^1").

Lemma le2_lohi : ltac2:(zQ "f0!l6!n9!k2!kl7!h9!jm4!jtb!lt1!j4!l0!jv5!hh8!pi3!hk4!hkb>2lo$4>2hi$4>0@2$3@2$6Z^2@2$7^2+hg0>0@2$3@2$6Z^2@2$7^2+hg0@3$a@1$8@1$1@1$0#8@1$c@1$b@2$d^4@2$e+hg0^3@3$2@1$1@1$0#8@1$5^4@3$2@1$1@1$0#8@1$5^3@1$9@1$1@1$0#8").
Proof.
  intros lo hi Hl Hh. unfold le2, wz, b8. rewrite unsigned_lit by lia. cbn [Z_to_le_bytes].
  f_equal; [apply Z_to_bv8_mod; rewrite <- Zplus_mod_idemp_r; replace (256 * hi) with (hi * 2^8) by lia; rewrite Z_mod_mult; rewrite Z.add_0_r; reflexivity|].
  f_equal. apply Z_to_bv8_mod. rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
  replace (lo + 256 * hi) with (lo + hi * 256) by lia. rewrite Z.div_add, Z.div_small by lia. reflexivity.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ticks_ok : ltac2:(zQ "10!s6>2st$0P") := ltac2:(zQ "h80!ih4!h9!pia!jb!j4!mme!mn5!jv5!mu7!mhe!mid!mvd!ng5!lu8!mg3!pj3!pje!plf!oh1!kl7!s6!pm5!pmd!po9\2st$h4@2$h3>3rid$0>2sh$2>1u$1>2hl@1$4@2$3$1$0>2ch@2$3$1$0>0@3$7@1$6$2@6$8$0$2@4$b$0$d$9$2@4$c$0$d$9$2^5@1$f^6@2$5$2^4>0@3$7@1$6@1$4@2$3$1$0@6$8$1@1$4@2$3$1$0@4$b$1$e$a@1$4@2$3$1$0@4$c$1$e$a@1$4@2$3$1$0^4@1$h5^5@2$5@1$4@2$3$1$0^3>0@3$h7@2$3$1$0^3^4@2$h1@3$h2$1$0^4@1$h0^9>3rid$0>2sh$2>2pg$1>1t$0>0@3$7@1$6$2@6$8$0$2@4$b$0$d$9$2@4$c$0$d$9$2^4@1$f^5@2$5$2^3>0@3$7@1$6$0@6$8$1$0@4$b$1$e$a$0@4$c$1$e$a$0^3@1$h6^4@2$5$0^2@2$h1^3@1$h0^7").


(* [comment removed for export] *)

(* [comment removed for export] *)
Definition wr_in : ltac2:(zQ "30!h9!ih4!s6>2st$2>3rid$1>1a$0>3len$0P") := ltac2:(zQ "h50!jr0!ih4!kl7!jtb!h9!hk4!mhe!lu8!mme!mn5!jv5!nhb!jt3!s6!jr9!nm7!nmf!og5!mu7!mvd!ng5\2st$d\3rid$1\1a$4\3len$4@2$b$0\1r$0@2$2@3$a@1$9$0@6$h2$1$0@4$h3$1$7$6$0@4$h4$1$7$6$0^4@1$h1^5@2$8$0^1@2$2@2$3@1$c^1^3@2$2@2$3@2$5^3^2@2$5@1$e^1@1$h0@1$f^1@2$3Z^2").

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma s_shadow_wr8 : ltac2:(zQ "hb0!ih4!h9!pia!jb!mvd!oi1!mhe!lu8!nua!mid!mg3!pj3!pof!pq9!pr7!k9!oh1!jv5!lm2!pse!s6!pt9!pm5!pmd!pje!pu3!nj9>2st$h4>1p$h2>1v$1@3$h1@4$4$0$7$6$2@1$b@3$h9^2^1^3@7$c$0$2@4$4$0$7$6$2@4$d$0$2@4$4$0$7$6$2@4$e$0$7$6$2@3$5$0$1^2@3$h3@7$c$1@2$3$1$0@4$4$1$a$9@2$3$1$0@4$d$1@2$3$1$0@4$4$1$a$9@2$3$1$0@4$e$1$a$9@2$3$1$0@3$h0$0$1^2@4$f$1$0@2$ha^1+vf@1$h8^3@1$h5@2$8^3@3$5$0$1^2@1$h6@2$8^3@3$5$0$1^2@1$h7@2$8^3@3$5$0$1^2@1$b^3").
Proof. intros. reflexivity. Qed.

Lemma get_shadow_unfold : ltac2:(zQ "e0!pia!ih4!mhe!lu8!pu9!jv5!nua!s6!pj3!pue!mu7!mvd!ng5!qg6>2st$7>3rid$1@3$5$0@2$6^2^1@5$d$0$0@1$4$0$9@6$a$1$0@4$b$1$3$2$0@4$c$1$3$2$0^1@1$8^2").
Proof. reflexivity. Qed.

Lemma get_shadow_wr8_same : ltac2:(zQ "h80!h9!ih4!jb!oi1!nua!mid!mg3!mvd!k9!oh1!jv5!lm2!pse!s6!pt9!pm5!pmd!pje!pia!pu3!nj9!pof!pq9!pr7>2st$d>1p$b>1v$0@3$a$h2@2$4@3$h3^2^1^3@3$3$1$0^2@3$c@7$h5$0@2$2$0$1@4$7$0$6$5@2$2$0$1@4$h6$0@2$2$0$1@4$7$0$6$5@2$2$0$1@4$h7$0$6$5@2$2$0$1@3$9$1$0^2@4$8$0$1@2$h4^1+vf@1$h1^3@1$e@2$4^3@3$3$1$0^2@1$f@2$4^3@3$3$1$0^2@1$h0@2$4^3@3$3$1$0^2").
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_eq. reflexivity. Qed.

Lemma get_shadow_wr8_other : ltac2:(zQ "a0!ih4!h9!jv5!nua!oi1!jb!oi7!s6!pia!pu3>2st$7>1p@2$5$0$1>1v$1>3rid$0>0@1$6@3$2$0^1@3$4$0$1^3@3$2$8@2$3@3$9^4^3^5^2@2$3^5^2").
Proof. intros. rewrite (get_shadow_unfold (wr8 p v st)), s_shadow_wr8, lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_other : ltac2:(zQ "c0!h9!ih4!oi1!jv5!nt4!nua!jb!oh1!oi7!nu0!s6!pu3>2st$a>1p@2$6$1$0>1v$0>1o$0>0@1$8@3$3$0^1@3$7$1$0^3@3$3$9@2$4@2$5@3$b^4^3^5@3$2$1$0^4^2@2$4@2$5^5@3$2$1$0^4^2").
Proof. intros. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_ne by congruence. reflexivity. Qed.

Lemma cell_read_wr8_same : ltac2:(zQ "h00!h9!ih4!oi1!oh1!kl7!jv5!qh5!nsc!lm2!nt4!nu0!nua!s6!pu3!jtb!lt1>2st$c>1p$8>1v$0>0@1$6^3>0@2$4@2$eZ^2@2$f^2+hg0@3$5$a@2$9@2$b@3$d^4^3^5@3$2$1$0^4@3$3$1$0^4@1$7^3").
Proof.
  intros st p v [T1 T2] Hv. rewrite get_shadow_wr8_same. unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite lookup_insert_eq.
  replace (Z.land v 255) with v by (change 255 with (Z.ones 8); rewrite Z.land_ones, Z.mod_small by lia; reflexivity).
  unfold get_shadow. destruct (s_shadow st !! fst p) as [sh|] eqn:E; cbn.
  - assert (SP : stale_pg (r_havp sh !! (snd p `div` 4096)) (Some (s_tick st)) = false).
    { unfold stale_pg. destruct (r_havp sh !! (snd p `div` 4096)) eqn:E2; [|reflexivity].
      apply N.ltb_ge. eapply T2; eauto. }
    assert (SU : stale (default [] (r_hav sh !! (snd p `div` 16))) (snd p `mod` 16) (Some (s_tick st)) = false).
    { unfold stale. apply Bool.not_true_iff_false. rewrite existsb_exists. (intros nd_i7; ndestruct nd_i7 as ([cov t] & Hin & Hb)).
      destruct (r_hav sh !! (snd p `div` 16)) eqn:E3; cbn in Hin; [|contradiction].
      apply Bool.andb_true_iff in Hb. destruct Hb as [_ Hb]. apply N.ltb_lt in Hb.
      pose proof (T1 _ _ _ _ _ E E3 Hin) as HT. cbn [snd] in HT. exfalso. apply (N.lt_irrefl t). eapply N.le_lt_trans; [exact HT | exact Hb]. }
    rewrite SP, SU. reflexivity.
  - rewrite lookup_empty. cbn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ticks_ok_wr8 : ltac2:(zQ "50!qh5!h9!lm2!s6!pu3>2st$3>1p$2>1v$1>0@1$0^3@1$0@3$4^3^2^4").
Proof.
  intros st p v [T1 T2]. split.
  - intros rid sh u hl ch Hs Hu Hin. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hu.
      unfold get_shadow in Hu. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hu.
      * eapply T1; eauto.
      * rewrite lookup_empty in Hu. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T1; eauto.
  - intros rid sh pg t Hs Hp. cbn [s_tick wr8 upd_shadow set_shadow] in *.
    rewrite s_shadow_wr8 in Hs. destruct (N.eq_dec rid (fst p)) as [->|NE].
    + rewrite lookup_insert_eq in Hs. inversion Hs; subst sh. cbn in Hp.
      unfold get_shadow in Hp. destruct (s_shadow st !! fst p) as [sh0|] eqn:E; cbn in Hp.
      * eapply T2; eauto.
      * rewrite lookup_empty in Hp. discriminate.
    + rewrite lookup_insert_ne in Hs by congruence. eapply T2; eauto.
Qed.

Lemma wr8_mod : ltac2:(zQ "60!s6!pu3!jv5!h9!lm2!oh7>2st$0>1p$4>1v$3@3$2$0@3$1^2^1^3@3$1^2@2$5^1+hg0^3").
Proof.
  intros. unfold wr8, upd_shadow. cbn beta.
  replace (Z.land (v mod 256) 255) with (Z.land v 255); [reflexivity|].
  change 255 with (Z.ones 8). rewrite !Z.land_ones by lia. rewrite Z.mod_mod by lia. reflexivity.
Qed.

Lemma le2_split : ltac2:(zQ "f0!l6!n9!k2!jm4!j4!l0!kl7!jv5!h9!hh8!pi3!qi0!jtb!lt1!oh7>1v$8>0@2$6@2$cZ^1@2$d^1+hggg0@3$7@1$4@1$1@1$0#8@1$a@1$9^2@3$2@1$1@1$0#8@1$3@2$e^2+hg0@3$2@1$1@1$0#8@1$3@2$b^2+hg0@1$5@1$1@1$0#8").
Proof.
  intros v Hv. replace v with (v mod 256 + 256 * (v / 256)) at 1 by (pose proof (Z.div_mod v 256); lia).
  rewrite le2_lohi; [reflexivity| |]; [pose proof (Z.mod_pos_bound v 256); lia | split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]].
Qed.


(* [comment removed for export] *)
Lemma get_meta_rec_upd : ltac2:(zQ "80!hi5!ls2!ojf!lm2!jv5!qi7!s6!qj2>2st$6>1g$3>1f>0$0$0>2g'$3@3$4$0@2$1@3$7^3^2^4^1M2\0$2$0@2$5^1^3@1^2@2$1^4^3@2$1^4^1").
Proof.
  intros. unfold get_meta_rec at 1. unfold upd_meta, put_meta. cbn [s_metas set_metas].
  unfold aptr_eqb. destruct g as [gr go], g' as [gr' go']. cbn [fst snd].
  destruct (N.eqb_spec gr' gr); destruct (Z.eqb_spec go' go); cbn [andb]; subst;
    first [rewrite lookup_insert_eq; reflexivity | rewrite lookup_insert_ne by congruence; reflexivity].
Qed.

Lemma aptr_eqb_refl : ltac2:(zQ "50!ojf!ok6!jv5!lm2!qi7>1g$3@3$2$0@2$4^1^1$1").
Proof. intros [a b]. unfold aptr_eqb. cbn. rewrite N.eqb_refl, Z.eqb_refl. reflexivity. Qed.

(* [comment removed for export] *)
Lemma map_seq_upd : forall {X} (f g : nat -> X) (j : nat) (x : X) n s,
  (forall i, (s <= i < s + n)%nat -> g i = if Nat.eqb i j then x else f i) ->
  (s <= j)%nat ->
  map g (seq s n) = upd (map f (seq s n)) (j - s) x.
Proof.
  intros X f g j x n. induction n as [|n IH]; intros s Hg Hj; [reflexivity|].
  cbn [seq map]. destruct (Nat.eq_dec j s) as [->|NE].
  - rewrite Nat.sub_diag. cbn [upd]. rewrite Hg by lia. rewrite Nat.eqb_refl. f_equal.
    apply map_ext_in. intros i Hi. apply in_seq in Hi. rewrite Hg by lia.
    destruct (Nat.eqb_spec i s); [lia|reflexivity].
  - replace (j - s)%nat with (S (j - S s)) by lia. cbn [upd]. f_equal.
    + rewrite Hg by lia. destruct (Nat.eqb_spec s j); [lia|reflexivity].
    + apply IH; [intros; apply Hg; lia|lia].
Qed.

Lemma active_set_active : ltac2:(zQ "80!sf!ojf!h9!jk9!jv5!s6!qjd!qka>2st$5>2sc$2>1v$0>1i$2@3$4$0@2$3@3$6^3^2^4^1M1\0$1$0@2$7^1^3^2@2$3^4^1").
Proof.
  intros. unfold active, set_active, upd_ctx. cbn [ctx s_ctx c_active set_active_map].
  destruct v as [p|]; destruct (Z.eqb_spec i sc); subst.
  - rewrite lookup_insert_eq. reflexivity.
  - rewrite lookup_insert_ne by congruence. reflexivity.
  - rewrite lookup_delete_eq. reflexivity.
  - rewrite lookup_delete_ne by congruence. reflexivity.
Qed.

Lemma actives_set_active : ltac2:(zQ "f0!l6!kv2!n9!j4!kl7!jv5!h9!hsf!ql1!s6!sf!qjd!jtb!lt1!ql8>2st$9>2sc$6>1v$a>0@2$4@2$cZ^2@2$d^2+j0@3$5@1$3@1$2@1$0#k0@1$1@3$b^3^2^4@4$8@1$2@1$0#k0@1$1^4@1$e^3@2$7^4^2").
Proof.
  intros st sc v Hsc. unfold actives.
  replace (Z.to_nat sc) with (Z.to_nat sc - 0)%nat by lia.
  apply (map_seq_upd (fun i => pw st (active st (Z.of_nat i))) (fun i => pw (set_active sc v st) (active (set_active sc v st) (Z.of_nat i)))); [|lia].
  intros i Hi. rewrite active_set_active.
  assert (Hpw : forall q, pw (set_active sc v st) q = pw st q) by (intros [q|]; reflexivity).
  rewrite Hpw. destruct (Z.eqb_spec (Z.of_nat i) sc); destruct (Nat.eqb_spec i (Z.to_nat sc)); try reflexivity; lia.
Qed.

(* [comment removed for export] *)
Definition sh_ticks : ltac2:(zQ "20!ih4!pia>2sh$1>1t$0P") := ltac2:(zQ "h30!h9!ih4!jb!j4!mid!mg3!mme!mn5!jv5!plf!mu7!mvd!ng5!oh1!kl7!pm5!pmd!pia!po9\2sh$h1\1t$1@2$e>1u$0>2hl@1$3@2$2$0$1>2ch@2$2$0$1>0@3$8@1$7@1$3@2$2$0$1@6$a$0@1$3@2$2$0$1@4$b$0$5$4@1$3@2$2$0$1@4$c$0$5$4@1$3@2$2$0$1^3@1$f^5@2$6@1$3@2$2$0$1^2>0@3$h2@2$2$0$1^2^3@2$9@3$d$0$1^3^6>2pg$0>2t'$1>0@3$8@1$7$1@6$a$0$1@4$b$0$5$4$1@4$c$0$5$4$1^2@1$h0^4@2$6$1^1@2$9^2^4").

Definition shadow_le : ltac2:(zQ "10!pia>2sh$0>3sh'$0P") := ltac2:(zQ "d0!h9!jv5!nsc!nt4!nu0!pt9!pia!jb!kl7!ih4!mid!mvd!mg3\2sh$6\3sh'$6@2$8@3$1@4$b$0$c$a@2$7$0$9@1$5^1@1$5^2>1o$0>1v$0>0@3$1$4@2$3^3^2@1$2^1@3$1$4@2$3^5^3@1$2^2").

Lemma shadow_le_refl : ltac2:(zQ "20!qm2!pia>2sh$1@2$0^1^1"). Proof. intros; split; auto. Qed.
Lemma shadow_le_trans : ltac2:(zQ "20!qm2!pia>1a$1>1b$1>1c$1>0@2$0^3^2>0@2$0^3^2@2$0^5^3").
Proof. intros a b c [E1 H1] [E2 H2]. split; [congruence|]. eauto. Qed.

Lemma In_filter_bool : forall {A} (f : A -> bool) (l : list A) x,
  In x (filter (fun y => f y) l) <-> In x l /\ f x = true.
Proof.
  intros A f l x. rewrite <- !list_elem_of_In. rewrite list_elem_of_filter.
  unfold Is_true. destruct (f x); intuition congruence.
Qed.

Lemma stale_hav_add : ltac2:(zQ "d0!ih4!h9!jb!ojf!qme!jv5!qn6!j4!mn5!oh1!qne!po9!plf>2hl@1$7@2$2$1$0>3cov$1>1t$0>1b$1>2tc@1$8$0>0>2ch@2$2$1$0>0@3$b@2$2$1$0^1^6@2$c@3$9$1$0^2^5>0@3$5$3@3$6@3$a^5^4^6^3^2$4@3$5$3@3$6^7^4^3$4").
Proof.
  intros hl cov t b tc Ht Hs. unfold stale in *.
  apply Bool.not_true_iff_false. apply Bool.not_true_iff_false in Hs. rewrite existsb_exists in *.
  (intros nd_i8; ndestruct nd_i8 as ([c' h'] & Hin & Hb)). apply Hs. cbn [fst snd] in Hb.
  apply Bool.andb_true_iff in Hb. destruct Hb as [Hb1 Hb2]. apply Z.ltb_lt in Hb1.
  destruct (Z.ltb_spec cov c').
  - exists (c', h'). split; [|cbn [fst snd]; rewrite (proj2 (Z.ltb_lt _ _) Hb1), Hb2; reflexivity].
    unfold hav_add. right. apply In_filter_bool. split; [exact Hin|]. cbn. apply Z.ltb_lt. assumption.
  - exists (cov, t). split; [unfold hav_add; left; reflexivity|]. cbn [fst snd].
    rewrite (proj2 (Z.ltb_lt _ _)) by lia. cbn [andb].
    destruct tc as [tc|]; [|reflexivity]. apply N.ltb_lt. apply N.ltb_lt in Hb2.
    pose proof (Ht _ Hin) as Hh. cbn [snd] in Hh. eapply N.lt_le_trans; [exact Hb2|exact Hh].
Qed.

Lemma hav_unit_step : ltac2:(zQ "h46!h9!ih4!jb!j4!mid!mg3!mvd!pse!pu9!l0!qo8!qne!pof!mu7!pq9!ng5!pr7!qg6!kl7!qm2&@4$e$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$h0$0$5$4@1$3@2$2$0$1&@6$d$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1@4$f$0$5$4@1$3@2$2$0$1^4^6&@5$h1@1$3@2$2$0$1@1$3@2$2$0$1@1$8@1$3@2$2$0$1@1$9@2$2$0$1~1&@3$b^3^2~2&@7$c$0@1$3@2$2$0$1@4$6$0$5$4@1$3@2$2$0$1~0^4~3^6&@3$7^7~4^5>5cells@4$6$0$5$4@2$2$0$1>3hav@4$6$0$5$4@1$3@2$2$0$1>4havp@4$6$0$5$4$1>1u$0>3cov$0>1t$1>0@2$a@3$7^6^5^4^1@2$h2@2$h3@3$7^7^6^5~5@2$a~5^2").
Proof.
  intros cells hav havp u cov t [T1 T2]. cbn [r_hav r_havp] in T1, T2.
  assert (Hl : forall ch, In ch (default [] (hav !! u)) -> (snd ch <= t)%N).
  { intros ch Hin. destruct (hav !! u) eqn:E2; cbn in Hin; [eapply T1; eauto| contradiction]. }
  split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 16) u) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. cbn [default from_option id] in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|].
      * destruct (stale_pg (havp !! (o / 4096)) (Some tc)) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) (Some tc)) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
      * destruct (stale_pg (havp !! (o / 4096)) None) eqn:SP; [cbn in Hc; discriminate|].
        destruct (stale (hav_add cov t (default [] (hav !! u))) (o mod 16) None) eqn:SU; [cbn in Hc; discriminate|].
        rewrite (stale_hav_add _ _ _ _ _ Hl SU). exact Hc.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [|exact T2].
    intros u' hl ch Hu Hin. destruct (Z.eq_dec u' u) as [->|NE].
    + rewrite lookup_insert_eq in Hu. inversion Hu; subst hl. unfold hav_add in Hin. destruct Hin as [<-|Hin]; [cbn; lia|].
      apply In_filter_bool in Hin. destruct Hin as [Hin _]. apply Hl. exact Hin.
    + rewrite lookup_insert_ne in Hu by congruence. eapply T1; eauto.
Qed.

Lemma hav_page_step : ltac2:(zQ "e3!h9!ih4!mid!mg3!mvd!pse!jb!qo8!pof!pq9!pr7!j4!kl7!qm2&@4$9$0$1@4$4$0$3$2$1@4$a$0$3$2$1&@7$8$0$1@4$4$0$3$2$1~0^3^2^4&@3$5^6^5~1>5cells@4$4$0$3$2@2$6$0$1>3hav@4$4$0$3$2@1$b@2$6$0$1>4havp@4$4$0$3$2$1>2pg$0>1t$1>0@2$7@3$5^5^4^3^1@2$c@2$d@3$5^6^5^4~2@2$7~2^2").
Proof.
  intros cells hav havp pg t [T1 T2]. cbn [r_hav r_havp] in T1, T2. split.
  - split; [reflexivity|]. intros o v Hc. unfold cell_read in *. cbn [r_cells r_hav r_havp] in *.
    destruct (Z.eq_dec (o / 4096) pg) as [E|NE].
    + rewrite E, lookup_insert_eq in Hc. rewrite E.
      destruct (cells !! o) as [[v0 tc]|]; cbn [stale_pg orb] in Hc.
      * destruct (N.ltb_spec tc t); [discriminate|].
        destruct (havp !! pg) as [h|] eqn:E2; cbn [stale_pg].
        -- pose proof (T2 _ _ E2). replace (tc <? h)%N with false by (symmetry; apply N.ltb_ge; lia). exact Hc.
        -- exact Hc.
      * discriminate.
    + rewrite lookup_insert_ne in Hc by congruence. exact Hc.
  - split; cbn [r_hav r_havp]; [exact T1|].
    intros pg' t' Hp. destruct (Z.eq_dec pg' pg) as [->|NE].
    + rewrite lookup_insert_eq in Hp. inversion Hp; subst. lia.
    + rewrite lookup_insert_ne in Hp by congruence. eapply T2; eauto.
Qed.

Lemma Z_iter_invariant : forall {A} (f : A -> A) (Inv : A -> Prop) n x,
  (forall y, Inv y -> Inv (f y)) -> Inv x -> Inv (Z.iter n f x).
Proof.
  intros A f Inv n x Hf Hx. destruct n; cbn; auto. apply Pos.iter_invariant; auto.
Qed.

Lemma havoc_units_le : ltac2:(zQ "c0!h9!ih4!pse!mid!mvd!mg3!jb!qo8!qp3!j4!kl7!qm2>5cells@4$4$0$5$3@2$6$0$1>3hav@4$4$0$5$3@1$9@2$6$0$1>4havp@4$4$0$5$3$1>1x$0>1y$0>1t$1>0@2$7@3$2^6^5^4^1@2$a@2$b@3$2^7^6^5@3$2^7@4$8^4^3^2^6^5@2$7@3$2^7@4$8^4^3^2^6^5^2").
Proof.
  intros cells hav havp x y t T. unfold havoc_units.
  set (f := fun acc : Z * gmap Z (list (Z * N)) => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells (snd acc) havp)
                                         /\ sh_ticks (mkShadow cells (snd acc) havp) t)).
  - intros [u h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_unit_step cells h havp u (if u =? (y - 1) / 16 then (let r := y mod 16 in if r =? 0 then 16 else r) else 16) t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma havoc_pages_le : ltac2:(zQ "c0!h9!ih4!pse!mid!mvd!mg3!jb!qo8!qq1!j4!kl7!qm2>5cells@4$4$0$5$3@2$6$0$1>3hav@4$4$0$5$3@1$9@2$6$0$1>4havp@4$4$0$5$3$1>2p0$0>2p1$0>1t$1>0@2$7@3$2^6^5^4^1@2$a@2$b@3$2^7^6^5@3$2^7^6@4$8^4^3^2^5@2$7@3$2^7^6@4$8^4^3^2^5^2").
Proof.
  intros cells hav havp p0 p1 t T. unfold havoc_pages.
  set (f := fun acc : Z * gmap Z N => _).
  apply (Z_iter_invariant f (fun acc => shadow_le (mkShadow cells hav havp) (mkShadow cells hav (snd acc))
                                         /\ sh_ticks (mkShadow cells hav (snd acc)) t)).
  - intros [pg h] [HL HT]. unfold f. cbn [fst snd].
    destruct (hav_page_step cells hav h pg t HT) as [HL2 HT2].
    split; [eapply shadow_le_trans; eauto| exact HT2].
  - cbn [snd]. split; [apply shadow_le_refl| exact T].
Qed.

Lemma sh_ticks_of_ticks_ok : ltac2:(zQ "60!ih4!qo8!qh5!nua!s6!pje>2st$4>3rid$0>0@1$2^2@2$1@2$3^3^2@1$5^3").
Proof.
  intros st rid [T1 T2]. unfold get_shadow. destruct (s_shadow st !! rid) as [sh|] eqn:E; cbn.
  - split; [intros; eapply T1; eauto | intros; eapply T2; eauto].
  - split; cbn; intros; rewrite lookup_empty in *; discriminate.
Qed.

(* [comment removed for export] *)

Lemma ticks_ok_set_tick : ltac2:(zQ "60!qh5!ih4!s6!pje!qqf!plf>2st$2>1t$1>0@2$5@1$3^2^1>0@1$0^3@1$0@2$4^3^4").
Proof.
  intros st t Ht [T1 T2]. split; cbn.
  - intros rid sh u hl ch H1 H2 H3. pose proof (T1 rid sh u hl ch H1 H2 H3). lia.
  - intros rid sh pg t' H1 H2. pose proof (T2 rid sh pg t' H1 H2). lia.
Qed.
(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
