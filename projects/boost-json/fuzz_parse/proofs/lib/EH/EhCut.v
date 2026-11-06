(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~04expr04EVar37Corelib7Numbers7BinNumsl11Z37Corelib4Init9Datatypesme3natme4bool46Stdlib5Arith8PeanoNat3Natp33eqb37Corelib4Init3Natr43add89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~sc4RATPsc3vGP04ELit3h5LinuxProcessSemantics5Riscv5Instrhhe7ALU_ADD04EAlume4listme4prodme4consme4pairme3nil06kentry04KImgme3appme3fstme3snd37Corelib5Lists7ListDefhp53mapsc9IMG_WORDS05KWord02SAsc3litsc7vCANARYsc5vAUXVsc4vRNDsc4vUIDsc4vX12sc4vX16sc4vX23sc3vX6sc7USP_OFFsc3addsc2vA05saddrsc7CUR_OFF46Stdlib6ZArith6BinInt1Zij13addsc2cbscbfslots_fromscbxslots_from03KWrsc4vHDRsc4vP2Vsc4sitesc7s_fsizesc7s_savedsc8saved_knsc3vRAsc4vSPFij13subsc3ZLOsc3ZHIme4truescaLOCALS_OFFsc2cvsc7auxv_knsc9cursor_knsc8flags_knsc8geomT_knsc6hdr_knsc6img_knsccstepframe_knsc8frame_knsc8geomB_knsc6cut1_Bsc6cut1_Tsc3uspsc4vS10sc4vS11sc3vS5sc3vS8sc3vS909sym_stateme4Nonesc2NXsc7cut1_knsc9cut1_regs03SSR06sentryhp53seqsc7CUT1_PCsc5s_padsch0P1_HANDLER_FOUNDij13eqb" s.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT.
Definition vA := EVar 0. Definition vHDR := EVar 2. Definition vAUXV := EVar 3. Definition vGP := EVar 4.
Definition vS5 := EVar 19. Definition vS8 := EVar 20. Definition vS9 := EVar 21. Definition vS10 := EVar 22. Definition vS11 := EVar 23.
Definition vX16 := EVar 24. Definition vUID := EVar 25. Definition vRND := EVar 26. Definition vP2V := EVar 27. Definition vCANARY := EVar 28.
Definition vX6 := EVar 29. Definition vX12 := EVar 30. Definition vX23 := EVar 31.
Definition vIP := EVar 32. Definition vSPF := EVar 34.
Definition RATP : Z := 0x10b6b8.
(* [comment removed for export] *)
Definition xslot : ltac2:(zQ "20!o6!k5>1i$0$1") := ltac2:(zQ "90!oc!k5!qe!o6!s6!hgb!hh2!hh8!kb\1i$3M0\0$0$1@2$2^1N3$6M0\0$0$1@2$2^1N4@1$7$5@1$8@2$4Ni0^1").
Definition fslot : ltac2:(zQ "20!o6!k5>1j$0$1") := ltac2:(zQ "30!o6!s6!kb\1j$0@1$2@2$1Nk0^1").
Definition vRA := EVar 110.
Definition sslot : ltac2:(zQ "20!o6!k5>1k$0$1") := ltac2:(zQ "30!o6!s6!kb\1k$0@1$2@2$1Nmf^1").
Definition NX : nat := 200%nat.
Definition lit : ltac2:(zQ "20!ma!k5>1z$0$1") := ltac2:(zQ "20!ma!hh8\1z$0@1$1^1").
Definition add : ltac2:(zQ "20!k5!ma>1e$0>1k$1$0") := ltac2:(zQ "50!ma!hk2!hkd!hh8!k5\1e$4\1k$0@3$2$1^2@1$3^1").
Definition ZLO : Z := -22736.     (* [comment removed for export] *)

(* [comment removed for export] *)
Record site := mkSite {
  s_ip    : Z ;          (* [comment removed for export] *)
  s_fsize : Z ;          (* [comment removed for export] *)
  s_saved : list Z ;     (* [comment removed for export] *)
  s_pad   : Z            (* [comment removed for export] *)
}.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition IMG_WORDS : ltac2:(zQ "30!ma!hl3!hla@1$1@2$2$0$0") := ltac2:(zQ "50!ma!hla!hm1!hm8!hmf@3$2@2$1$0$0@4$3$0$0+vokt8+tknuc@3$2@2$1$0$0@4$3$0$0+voku0+tkoi4@3$2@2$1$0$0@4$3$0$0+voku8+tkos0@3$2@2$1$0$0@4$3$0$0+volg8+tkpu4@3$2@2$1$0$0@4$3$0$0+volh0+tkqsc@3$2@2$1$0$0@4$3$0$0+volh8+tkqv4@3$2@2$1$0$0@4$3$0$0+volj0+tkrq0@3$2@2$1$0$0@4$3$0$0+vomg0+vppq8@3$2@2$1$0$0@4$3$0$0+vomh8Z@3$2@2$1$0$0@4$3$0$0+voml8+vomg0@3$2@2$1$0$0@4$3$0$0+vomn0+pitqc@3$2@2$1$0$0@4$3$0$0+vomr8+vluq8@3$2@2$1$0$0@4$3$0$0+voms8+vppg0@3$2@2$1$0$0@4$3$0$0+vomt0+vpov8@3$2@2$1$0$0@4$3$0$0+vomt8+hgpso8@3$2@2$1$0$0@4$3$0$0+vonn0+hirmv8@3$2@2$1$0$0@4$3$0$0+vpnv0+pkuq8@3$2@2$1$0$0@4$3$0$0+vpov8+nnsq8@3$2@2$1$0$0@4$3$0$0+vppg0+nntr4@1$4@2$1$0$0").
Definition img_kn : ltac2:(zQ "20!hl3!hn5@1$0$1") := ltac2:(zQ "e0!ma!hn5!hm1!hla!hh8!hnd!ho3!ho9!hmf!hof!hqc!hr3!hrf!hs6@3$6$1@3$2$1@2$5+hggg0+kngg0@3$2$1@2$5+kngg0+vhgg0@1$8$1@4$a@2$3$0$0$1\2av@2$3$0$0@3$c@2$d@1$4Z@3$7$0$0^1N8@1$4@3$9$0$0^1$b").
(* [comment removed for export] *)
Definition newh_kn : ltac2:(zQ "20!hl3!hn5@1$0$1") := ltac2:(zQ "60!hh8!hn5!hm1!hmf!hrf!hs6@3$2$1@3$4@2$5@1$0Z+hgpso8N8@1$0Z@1$3$1").
(* [comment removed for export] *)
Definition flags_kn : ltac2:(zQ "20!hl3!hn5@1$0$1") := ltac2:(zQ "70!hsa!hn5!hm1!hrf!hs6!hmf!ht0@3$2$1@3$3@2$4@1$0Z+hirmv8N8$6@3$2$1@3$3@2$4@1$0Z+hgrlu1N1@1$0+1@3$2$1@3$3@2$4@1$0Z+hgrlu2N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hgrlu3N1@1$0+1@3$2$1@3$3@2$4@1$0Z+hgrlu4N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hgrlu5N1@1$0+1@3$2$1@3$3@2$4@1$0Z+hgrlu6N1@1$0Z@1$5$1").
(* [comment removed for export] *)
Definition auxv_kn : ltac2:(zQ "20!hl3!hn5@1$0$1") := ltac2:(zQ "d0!hn5!hm1!hta!hrf!hs6!hsa!hmf!hu2!hu9!hv0!hv7!hve!ig5@3$1$0@3$3@2$4@1$5Z+hirpl0N8$2@3$1$0@3$3@2$4$2ZN8@1$5+3@3$1$0@3$3@2$4$2+8N8@1$5+hggk0@3$1$0@3$3@2$4$2+h0N8@1$5+4@3$1$0@3$3@2$4$2+h8N8@1$5+j8@3$1$0@3$3@2$4$2+i0N8@1$5+5@3$1$0@3$3@2$4$2+i8N8@1$5+a@3$1$0@3$3@2$4$2+j0N8@1$5+h0@3$1$0@3$3@2$4$2+j8N8$a@3$1$0@3$3@2$4$2+k0N8@1$5+6@3$1$0@3$3@2$4$2+k8N8$c@3$1$0@3$3@2$4$2+l0N8@1$5+b@3$1$0@3$3@2$4$2+l8N8$8@3$1$0@3$3@2$4$2+m0N8@1$5+c@3$1$0@3$3@2$4$2+m8N8$9@3$1$0@3$3@2$4$2+n0N8@1$5+h7@3$1$0@3$3@2$4$2+n8N8$b@3$1$0@3$3@2$4$2+o0N8@1$5+h9@3$1$0@3$3@2$4$2+o8N8$7@3$1$0@3$3@2$4$2+p0N8@1$5Z@3$1$0@3$3@2$4$2+p8N8@1$5Z@1$6$0").

(* [comment removed for export] *)
Definition USP_OFF : ltac2:(zQ "20!oc!ma>6phase2$0$1") := ltac2:(zQ "20!oc!ma\6phase2$0M0\6phase2$0$1^1-ks0-ii0").   (* [comment removed for export] *)
Definition usp : ltac2:(zQ "20!oc!k5>6phase2$0$1") := ltac2:(zQ "40!oc!igb!ih5!ihb\6phase2$0@2$2$3@1$1^1").
Definition CUR_OFF : Z := 8.                                                (* [comment removed for export] *)
Definition UC_OFF : Z := 616.                                               (* [comment removed for export] *)
Definition cb : ltac2:(zQ "30!oc!ma!ii0>6phase2$0>3off$1$2") := ltac2:(zQ "60!oc!ma!ii7!ihb!hs6!ik9\6phase2$0\3off$1@2$4$3@2$5$2^1").
Definition cv : ltac2:(zQ "20!oc!k5>6phase2$0$1") := ltac2:(zQ "40!oc!ii7!ih5!ihb\6phase2$0@2$2$3$1").
Fixpoint xslots_from (phase2 : bool) (i : nat) (n : nat) : list kentry :=
  match n with O => [] | S n' =>
    KWord (cb phase2 (16 + 8 * Z.of_nat i)) 8 (xslot i) :: xslots_from phase2 (S i) n' end.
Fixpoint fslots_from (phase2 : bool) (j : nat) (n : nat) : list kentry :=
  match n with O => [] | S n' =>
    KWord (cb phase2 (272 + 8 * Z.of_nat j)) 8 (fslot j) :: fslots_from phase2 (S j) n' end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cursor_kn : ltac2:(zQ "30!oc!hl3!hn5>6phase2$0@1$1$2") := ltac2:(zQ "c0!hn5!hm1!il0!hrf!kb!hsa!ho3!hmf!oc!il5!im3!in1\6phase2$8@3$6$0@3$1$0@3$3@2$2^1ZN8@1$5+voks8@3$1$0@3$3@2$2^1+8N8@1$5+hgrlu0@1$7$0@3$6$0@3$a^1N0Ni0@3$6$0@3$9^1N0Ni0@3$1$0@3$3@2$2^1+ih0N8@1$4Nm0@3$1$0@3$3@2$2^1+ih8N8@1$4Nm1@3$1$0@3$3@2$2^1+ii0N8@1$4Nm2@3$1$0@3$3@2$2^1+ii8N8@1$4Nm3@3$1$0@3$3@2$2^1+ij0N8@1$4Nm4@3$1$0@3$3@2$2^1+ij8N8@1$4Nm5@3$1$0@3$3@2$2^1+ik0N4@1$4Nm6@3$1$0@3$3@2$2^1+ik4N4@1$4Nma@3$1$0@3$3@2$2^1+ik8N8@1$4Nm7@3$1$0@3$3@2$2^1+il0N8@1$4Nm8@3$1$0@3$3@2$2^1+il8N1@1$5Z@3$1$0@3$3@2$2^1+il9N1@1$5Z@3$1$0@3$3@2$2^1+ilaN1@1$4Nm9@3$1$0@2$b@2$2^1Z@1$5+im0@1$7$0").

(* [comment removed for export] *)
Definition hdr_kn : ltac2:(zQ "30!oc!hl3!hn5>6phase2$0@1$1$2") := ltac2:(zQ "h00!hn5!in6!hm1!hsa!hs6!hrf!oc!hmf!ma!ho3!k5!hl3!o6!ih5!ind!in1\6phase2$6@3$9$0@3$2$0@3$5@2$4$1+8N8@1$3+1@3$2$0@3$5@2$4$1+h0N8@1$3+vluq8@3$2$0@3$5@2$4$1+h8N8@1$3+pitqc@3$2$0@3$5@2$4$1+i0N8@1$3+nntr4@3$2$0@3$5@2$4$1+i8N8@1$3+nnsq8@3$2$0@3$5@2$4$1+j0N8@1$3Z@3$2$0@3$5@2$4$1+j8M6\6phase2$6$c^1N4N8@1$3Z@1$7$0@3$9$0M6\6phase2$6@1$b$0^1@3$2$0@3$5@2$4$1+jcN4@1$3+1@1$7$0@1$7$0@3$2$0@3$5@2$4$1+k0N8@1$3M6\6phase2$6$8^1+invofZ@3$2$0@3$5@2$4$1+k8N8@1$3M6\6phase2$6$8^1+invn0Z@3$2$0@3$5@2$4$1+l0N8@1$3M6\6phase2$6$8^1+knpp4Z@3$2$0@3$5@2$4$1+l8N8M6\6phase2$6$a^1@2$d$1+o0@1$3Z@3$2$0@3$5@2$4$1+m0N8@1$3+kjkskuknkjirirg0@3$2$0@3$5@2$4$1+m8N8@1$3+pkms8@3$2$0@3$5@2$4$1+n0N8@1$3Z@3$2$0@3$5@2$4$1+n8N8M6\6phase2$6$a^1$e@1$3Z@3$2$0@3$5@2$4$1+o0N8@1$3+vlug0@3$2$0@2$f@2$4$1Z@1$3+p0@1$7$0").                     (* [comment removed for export] *)

Fixpoint saved_kn (fsize : Z) (offs : list Z) (k : nat) : list kentry :=
  match offs with [] => [] | off :: r => KWord (SA vSPF (fsize + off)) 8 (sslot k) :: saved_kn fsize r (S k) end.
Definition frame_kn : ltac2:(zQ "30!hl3!io4!hn5>2st$1@1$0$2") := ltac2:(zQ "b0!iob!hm1!ip5!ipf!io4!iqa!ir0!hrf!hs6!hn5!ir7\2st$4@3$1$9@3$7@2$8$6@2$a@1$0^1+8N8$5@3$3@1$0^1@1$2^1N0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ZHI : ltac2:(zQ "20!oc!ma>6phase2$0$1") := ltac2:(zQ "20!oc!ma\6phase2$0M0\6phase2$0$1^1+im8+nk0").   (* [comment removed for export] *)
Definition Ureg : ltac2:(zQ "40!oc!hla!k5!ii0>6phase2$0@2$1$3$2") := ltac2:(zQ "a0!ire!oc!hm8!is4!hsa!ihb!hs6!k5!ii0!ir7\6phase2$1@4$2$8$7@2$6$5$0@1$4@2$9@1$3^1$0").
Definition geomT_kn (phase2 : bool) : list kentry :=
  let '(U, Un) := Ureg phase2 in
  let H := SA vHDR 0 in let Hn := lit 144 in
  let A := SA vAUXV 0 in let An := lit 160 in
  [KDisj U Un H Hn; KDisj U Un A An; KDisj H Hn A An;
   KDisj H Hn (SA (lit 0) 0x10b5e0) (lit 8); KDisj H Hn (SA (lit 0) 0x12b6f8) (lit 8); KDisj H Hn (SA (lit 0) 0x12b950) (lit 8);
   KDisj H Hn (SA (lit 0) 0x10000) (lit 0xe1000); KDisj H Hn (SA (lit 0) 0xf84d8) (lit 0x1430);   (* [comment removed for export] *)
   KRange vA 0x400000000000 0x800000000000; KRange vAUXV 0x400000000000 0xffffffffffffff60;
   KRange vHDR 1 0x800000000000;
   KAlign vA 16; KAlign vHDR 16].
(* [comment removed for export] *)
Definition geomB_kn (phase2 : bool) (catchframe : bool) (st : site) : list kentry :=
  let '(U, Un) := Ureg phase2 in
  let H := SA vHDR 0 in let Hn := lit 144 in
  let F := SA vSPF 0 in let Fn := lit (s_fsize st) in
  [KRange vIP (s_ip st) (s_ip st);
   KDisj U Un F Fn; KDisj H Hn F Fn;      (* [comment removed for export] *)
   KRange vSPF 0x400000000000 0x800000000000; KAlign vSPF 16]
  ++ (if phase2 then [KRange vP2V 0x400000000000 0x800000000000;
                      if catchframe then KRange (EAlu ALU_SUB vP2V vSPF) 0 0 else KRange (EAlu ALU_SUB vP2V vSPF) 16 0x800000000000] else []).

(* [comment removed for export] *)
Definition LOCALS_OFF : ltac2:(zQ "20!oc!ma>6phase2$0$1") := ltac2:(zQ "30!oc!ma!ik9\6phase2$0M0\6phase2$0$1^1@2$2-iq0+ig8+mn8").   (* [comment removed for export] *)
Definition stepframe_kn : ltac2:(zQ "30!oc!hl3!hn5>6phase2$0@1$1$2") := ltac2:(zQ "h40!hn5!hm1!ihb!hs6!oc!igb!hsa!ik9!hrf!ire!in1!hmf!isa!ma!it1!ih5!ite!in6!k5!ir7\6phase2$4@3$1$0@3$8@2$3$2@2$7@1$5^1+ig0N8M4\6phase2$4$h2^1@1$h0$c@1$6+hhhle@3$1$0@3$8@2$3$2@2$7@1$5^1+ig8N8@1$6+vppq8@3$1$0@3$8@2$3$2@2$7@1$5^1+ih0N8@2$f$h1+m0@3$1$0@3$8@2$3$2@2$7@1$5^1+ih8N8@1$6M4\6phase2$4$d^1+tiui0+tiri8@3$1$0@2$a@2$3$2$9@1$6@2$h3@2$7@1$5^1+ii0$9@3$1$0@2$a@2$3$2@1$e^1@1$6+l0@1$b$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cut1_T : ltac2:(zQ "30!oc!hl3!hn5>6phase2$0@1$1$2") := ltac2:(zQ "a0!ho3!hn5!oc!iu3!iud!iv9!jg4!jgf!jh8!ji1\6phase2$2@3$0$1@1$9^1@3$0$1@1$4^1@3$0$1@1$7^1@3$0$1$5@3$0$1$3@3$0$1$8@1$6^1").
Definition cut1_B : ltac2:(zQ "40!oc!hl3!io4!hn5>6phase2$0>acatchframe$0>2st$2@1$1$3") := ltac2:(zQ "60!oc!ho3!jj0!jjb!io4!hn5\6phase2$0\acatchframe$0\2st$4@3$1$5@1$2^1@3$3^3^2^1").
Definition cut1_kn : ltac2:(zQ "40!oc!hl3!io4!hn5>6phase2$0>acatchframe$0>2st$2@1$1$3") := ltac2:(zQ "60!oc!ho3!jk6!jkf!io4!hn5\6phase2$0\acatchframe$0\2st$4@3$1$5@1$3^3@3$2^3^2^1").

(* [comment removed for export] *)
Definition cut1_regs : ltac2:(zQ "30!oc!hl3!k5>6phase2$0@1$1$2") := ltac2:(zQ "h00!k5!hm1!kb!hsa!oc!ma!hmf!hgb!ite!jl8!hh2!jle!jm5!jmc!jn2!jn8\6phase2$4@3$1$0@1$3Z@3$1$0@1$3+tkqpc@3$1$0@1$9^1@3$1$0$a@3$1$0@1$3$7@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0@1$8^1@3$1$0@1$3+hgrlu0@3$1$0@1$3+1@3$1$0@1$2N8@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$3M4\6phase2$4$5^1+1Z@3$1$0@1$3M4\6phase2$4$5^1+hjpja+hhrqe@3$1$0@1$3M4\6phase2$4$5^1+hilt8+hiht5@3$1$0$d@3$1$0@1$3+hhpg8@3$1$0@1$3+8@3$1$0$e@3$1$0$f@3$1$0$b@3$1$0$c@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@1$6$0").

Definition cut1 : ltac2:(zQ "30!oc!io4!jne>6phase2$0>acatchframe$0>2st$1$2") := ltac2:(zQ "a0!oc!jo9!hmf!jp0!jp5!jpf!io4!jqb!ii0!jr0\6phase2$0\acatchframe$0\2st$6@6$7+tkqpc@1$5^3@1$2$9@3$4^3^2^1$3@1$1$8").

(* [comment removed for export] *)
Definition PV : ltac2:(zQ "20!hl3!o6@1$0$1") := ltac2:(zQ "50!o6!ho3!jr8!hm1!hmf@3$1$0@2$2N5Nf@3$1$0@3$3$0Ni0@3$3$0Ni1@3$3$0Ni2@1$4$0@3$1$0@2$2Ni5Nhb@3$1$0@2$2Nk0Ni0@2$2Nm0Nb").                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CUT1_PC : Z := 0xd4a9c.
Definition P1_HANDLER_FOUND : Z := 0xd2c6c.
Definition ends : ltac2:(zQ "40!oc!hl3!ma!io4>6phase2$0>2st$3@1$1$2") := ltac2:(zQ "a0!ma!oc!hm1!hmf!jrf!hl3!js9!jt1!io4!ju5\6phase2$1\2st$8M1\6phase2$1@1$5$0^2M1\0$1@1$5$0@2$9@1$6^1Z@3$2$0$4@1$3$0@3$2$0$4@3$2$0@1$6^1@1$3$0@3$2$0$4@3$2$0$7@1$3$0").
End CUT.
(* [comment removed for export] *)
