(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XAxSymExec3.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~04expr04EVar37Corelib7Numbers7BinNumsl11Z37Corelib4Init9Datatypesme3natme4bool46Stdlib5Arith8PeanoNat3Natp33eqb37Corelib4Init3Natr43add04ELit89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3EHU5EhCut3CUT~~~~~~t24RATPt23vGP3h5LinuxProcessSemantics5Riscv5Instrhhf7ALU_ADD04EAlume4listme4prodme4consme4pairme3nil06kentry04KImgme3appme3fstme3snd37Corelib5Lists7ListDefhp63map05KWord02SAt29IMG_WORDSt23litt27vCANARYt25vAUXVt24vRNDt24vUIDt24vX12t24vX16t24vX23t23vX6t27USP_OFFt23addt22vA05saddrt27CUR_OFF46Stdlib6ZArith6BinInt1Zij23addt22cb03KWrt2bfslots_fromt2bxslots_fromt24vHDRt24vP2Vt24sitet27s_fsizet24vSPF04KUnkt27s_savedt28saved_knt23vRAij23subt23ZLOt23ZHIme4truet2aLOCALS_OFFt22cvt27auxv_knt29cursor_knt28flags_knt28geomT_knt26hdr_knt26img_knt2cstepframe_knt28frame_knt28geomB_knt26cut1_Bt26cut1_Tt23uspt24vS10t24vS11t23vS5t23vS8t23vS909sym_stateme4None03SSR06sentryt22NXt27cut1_knt29cut1_regshp63seqt27CUT1_PCt25s_padt2h0P1_HANDLER_FOUNDij23eqb" s.
Import ListNotations. Import AX2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module CUT.
Definition vA := EVar 0. Definition vHDR := EVar 2. Definition vAUXV := EVar 3. Definition vGP := EVar 4.
Definition vS5 := EVar 19. Definition vS8 := EVar 20. Definition vS9 := EVar 21. Definition vS10 := EVar 22. Definition vS11 := EVar 23.
Definition vX16 := EVar 24. Definition vUID := EVar 25. Definition vRND := EVar 26. Definition vP2V := EVar 27. Definition vCANARY := EVar 28.
Definition vX6 := EVar 29. Definition vX12 := EVar 30. Definition vX23 := EVar 31.
Definition vIP := EVar 32. Definition vSPF := EVar 34.
Definition RATP : Z := 0x10ebf8.
(* [comment removed for export] *)
Definition xslot : ltac2:(zQ "20!o6!k5>1i$0$1") := ltac2:(zQ "90!oc!k5!qe!o6!s6!sc!kb!hh2!hh9\1i$3M0\0$0$1@2$2^1N3$8M0\0$0$1@2$2^1N4@1$5$7@1$6@2$4Ni0^1").
Definition fslot : ltac2:(zQ "20!o6!k5>1j$0$1") := ltac2:(zQ "30!o6!s6!kb\1j$0@1$2@2$1Nk0^1").
Definition vRA := EVar 110.
Definition sslot : ltac2:(zQ "20!o6!k5>1k$0$1") := ltac2:(zQ "30!o6!s6!kb\1k$0@1$2@2$1Nmf^1").
Definition NX : nat := 200%nat.
Definition lit : ltac2:(zQ "20!ma!k5>1z$0$1") := ltac2:(zQ "20!ma!sc\1z$0@1$1^1").
Definition add : ltac2:(zQ "20!k5!ma>1e$0>1k$1$0") := ltac2:(zQ "50!ma!hk3!hke!sc!k5\1e$4\1k$0@3$2$1^2@1$3^1").
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
Definition IMG_WORDS : ltac2:(zQ "30!ma!hl4!hlb@1$1@2$2$0$0") := ltac2:(zQ "50!ma!hlb!hm2!hm9!hn0@3$2@2$1$0$0@4$3$0$0+vrpu0+tnsp4@3$2@2$1$0$0@4$3$0$0+vrpu8+tnssc@3$2@2$1$0$0@4$3$0$0+vrpv0+tntm8@3$2@2$1$0$0@4$3$0$0+vrqh0+tnuoc@3$2@2$1$0$0@4$3$0$0+vrqh8+tnvn4@3$2@2$1$0$0@4$3$0$0+vrqi0+tnvpc@3$2@2$1$0$0@4$3$0$0+vrqj8+togk8@3$2@2$1$0$0@4$3$0$0+vrrg8+vsuu8@3$2@2$1$0$0@4$3$0$0+vrri0Z@3$2@2$1$0$0@4$3$0$0+vrrm0+vrrg8@3$2@2$1$0$0@4$3$0$0+vrrn8+pmil4@3$2@2$1$0$0@4$3$0$0+vrrs0+vpjr0@3$2@2$1$0$0@4$3$0$0+vrrt0+vsuk0@3$2@2$1$0$0@4$3$0$0+vrrt8+vsuj8@3$2@2$1$0$0@4$3$0$0+vrru0+hgths8@3$2@2$1$0$0@4$3$0$0+vrsn8+hiusj8@3$2@2$1$0$0@4$3$0$0+vssv8+pojl0@3$2@2$1$0$0@4$3$0$0+vsuj8+nrhl0@3$2@2$1$0$0@4$3$0$0+vsuk0+nrilc@1$4@2$1$0$0").
Definition img_kn : ltac2:(zQ "20!hl4!hn6@1$0$1") := ltac2:(zQ "e0!ma!hn6!hm2!hlb!sc!hne!ho4!hoa!hn0!hp0!hqd!hr4!hrb!hrf@3$6$1@3$2$1@2$5+hggg0+kmgg0@3$2$1@2$5+kmgg0+vkgg0@1$8$1@4$a@2$3$0$0$1\2av@2$3$0$0@3$b@2$c@1$4Z@3$7$0$0^1N8@1$4@3$9$0$0^1$d").
(* [comment removed for export] *)
Definition newh_kn : ltac2:(zQ "20!hl4!hn6@1$0$1") := ltac2:(zQ "60!sc!hn6!hm2!hn0!hr4!hrb@3$2$1@3$4@2$5@1$0Z+hgths8N8@1$0Z@1$3$1").
(* [comment removed for export] *)
Definition flags_kn : ltac2:(zQ "20!hl4!hn6@1$0$1") := ltac2:(zQ "70!hsb!hn6!hm2!hr4!hrb!hn0!ht1@3$2$1@3$3@2$4@1$0Z+hiusj8N8$6@3$2$1@3$3@2$4@1$0Z+hguri1N1@1$0+1@3$2$1@3$3@2$4@1$0Z+hguri2N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hguri3N1@1$0+1@3$2$1@3$3@2$4@1$0Z+hguri4N1@1$0Z@3$2$1@3$3@2$4@1$0Z+hguri5N1@1$0+1@3$2$1@3$3@2$4@1$0Z+hguri6N1@1$0Z@1$5$1").
(* [comment removed for export] *)
Definition auxv_kn : ltac2:(zQ "20!hl4!hn6@1$0$1") := ltac2:(zQ "d0!hn6!hm2!hr4!hrb!htb!hsb!hn0!hu3!hua!hv1!hv8!hvf!ig6@3$1$0@3$2@2$3@1$5Z+hiuup0N8$4@3$1$0@3$2@2$3$4ZN8@1$5+3@3$1$0@3$2@2$3$4+8N8@1$5+hggk0@3$1$0@3$2@2$3$4+h0N8@1$5+4@3$1$0@3$2@2$3$4+h8N8@1$5+j8@3$1$0@3$2@2$3$4+i0N8@1$5+5@3$1$0@3$2@2$3$4+i8N8@1$5+a@3$1$0@3$2@2$3$4+j0N8@1$5+h0@3$1$0@3$2@2$3$4+j8N8$a@3$1$0@3$2@2$3$4+k0N8@1$5+6@3$1$0@3$2@2$3$4+k8N8$c@3$1$0@3$2@2$3$4+l0N8@1$5+b@3$1$0@3$2@2$3$4+l8N8$8@3$1$0@3$2@2$3$4+m0N8@1$5+c@3$1$0@3$2@2$3$4+m8N8$9@3$1$0@3$2@2$3$4+n0N8@1$5+h7@3$1$0@3$2@2$3$4+n8N8$b@3$1$0@3$2@2$3$4+o0N8@1$5+h9@3$1$0@3$2@2$3$4+o8N8$7@3$1$0@3$2@2$3$4+p0N8@1$5Z@3$1$0@3$2@2$3$4+p8N8@1$5Z@1$6$0").

(* [comment removed for export] *)
Definition USP_OFF : ltac2:(zQ "20!oc!ma>6phase2$0$1") := ltac2:(zQ "20!oc!ma\6phase2$0M0\6phase2$0$1^1-ks0-ii0").   (* [comment removed for export] *)
Definition usp : ltac2:(zQ "20!oc!k5>6phase2$0$1") := ltac2:(zQ "40!oc!igc!ih6!ihc\6phase2$0@2$2$3@1$1^1").
Definition CUR_OFF : Z := 8.                                                (* [comment removed for export] *)
Definition UC_OFF : Z := 616.                                               (* [comment removed for export] *)
Definition cb : ltac2:(zQ "30!oc!ma!ii1>6phase2$0>3off$1$2") := ltac2:(zQ "60!oc!ma!hrb!ii8!ihc!ika\6phase2$0\3off$1@2$2$4@2$5$3^1").
Definition cv : ltac2:(zQ "20!oc!k5>6phase2$0$1") := ltac2:(zQ "40!oc!ii8!ih6!ihc\6phase2$0@2$2$3$1").
Fixpoint xslots_from (phase2 : bool) (i : nat) (n : nat) : list kentry :=
  match n with O => [] | S n' =>
    KWord (cb phase2 (16 + 8 * Z.of_nat i)) 8 (xslot i) :: xslots_from phase2 (S i) n' end.
Fixpoint fslots_from (phase2 : bool) (j : nat) (n : nat) : list kentry :=
  match n with O => [] | S n' =>
    KWord (cb phase2 (272 + 8 * Z.of_nat j)) 8 (fslot j) :: fslots_from phase2 (S j) n' end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cursor_kn : ltac2:(zQ "30!oc!hl4!hn6>6phase2$0@1$1$2") := ltac2:(zQ "c0!hn6!hm2!il1!hr4!kb!hsb!ho4!hn0!oc!il6!ilb!im9\6phase2$8@3$6$0@3$1$0@3$3@2$2^1ZN8@1$5+vrpt0@3$1$0@3$3@2$2^1+8N8@1$5+hguri0@1$7$0@3$6$0@3$b^1N0Ni0@3$6$0@3$a^1N0Ni0@3$1$0@3$3@2$2^1+ih0N8@1$4Nm0@3$1$0@3$3@2$2^1+ih8N8@1$4Nm1@3$1$0@3$3@2$2^1+ii0N8@1$4Nm2@3$1$0@3$3@2$2^1+ii8N8@1$4Nm3@3$1$0@3$3@2$2^1+ij0N8@1$4Nm4@3$1$0@3$3@2$2^1+ij8N8@1$4Nm5@3$1$0@3$3@2$2^1+ik0N4@1$4Nm6@3$1$0@3$3@2$2^1+ik4N4@1$4Nma@3$1$0@3$3@2$2^1+ik8N8@1$4Nm7@3$1$0@3$3@2$2^1+il0N8@1$4Nm8@3$1$0@3$3@2$2^1+il8N1@1$5Z@3$1$0@3$3@2$2^1+il9N1@1$5Z@3$1$0@3$3@2$2^1+ilaN1@1$4Nm9@3$1$0@2$9@2$2^1Z@1$5+im0@1$7$0").

(* [comment removed for export] *)
Definition hdr_kn : ltac2:(zQ "30!oc!hl4!hn6>6phase2$0@1$1$2") := ltac2:(zQ "h00!hn6!in7!hm2!hrb!hsb!hr4!oc!hn0!ma!ho4!k5!hl4!o6!il6!ih6!ine\6phase2$6@3$9$0@3$2$0@3$5@2$3$1+8N8@1$4+1@3$2$0@3$5@2$3$1+h0N8@1$4+vpjr0@3$2$0@3$5@2$3$1+h8N8@1$4+pmil4@3$2$0@3$5@2$3$1+i0N8@1$4+nrilc@3$2$0@3$5@2$3$1+i8N8@1$4+nrhl0@3$2$0@3$5@2$3$1+j0N8@1$4Z@3$2$0@3$5@2$3$1+j8M6\6phase2$6$c^1N4N8@1$4Z@1$7$0@3$9$0M6\6phase2$6@1$b$0^1@3$2$0@3$5@2$3$1+jcN4@1$4+1@1$7$0@1$7$0@3$2$0@3$5@2$3$1+k0N8@1$4M6\6phase2$6$8^1+ioghfZ@3$2$0@3$5@2$3$1+k8N8@1$4M6\6phase2$6$8^1+iogg0Z@3$2$0@3$5@2$3$1+l0N8@1$4M6\6phase2$6$8^1+knll0Z@3$2$0@3$5@2$3$1+l8N8M6\6phase2$6$a^1@2$e$1+o0@1$4Z@3$2$0@3$5@2$3$1+m0N8@1$4+kjkskuknkjirirg0@3$2$0@3$5@2$3$1+m8N8@1$4+pnrn0@3$2$0@3$5@2$3$1+n0N8@1$4Z@3$2$0@3$5@2$3$1+n8N8M6\6phase2$6$a^1$f@1$4Z@3$2$0@3$5@2$3$1+o0N8@1$4+vpjg8@3$2$0@2$d@2$3$1Z@1$4+p0@1$7$0").                     (* [comment removed for export] *)

Fixpoint saved_kn (fsize : Z) (offs : list Z) (k : nat) : list kentry :=
  match offs with [] => [] | off :: r => KWord (SA vSPF (fsize + off)) 8 (sslot k) :: saved_kn fsize r (S k) end.
Definition frame_kn : ltac2:(zQ "30!hl4!hn6!io5>2st$2@1$0$1") := ltac2:(zQ "f0!hn6!ioc!hm2!hrb!ip6!ho4!hn0!ipd!hr4!hsb!iq3!iqd!io5!ir8!ire\2st$c@3$5$0@3$2$0@3$8@2$3$4@2$e@1$1^1+8N8$d@3$b@1$1^1@1$a^1N0@3$2$0@2$7@2$3$4Z@1$9@1$1^1@1$6$0").   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ZHI : ltac2:(zQ "20!oc!ma>6phase2$0$1") := ltac2:(zQ "20!oc!ma\6phase2$0M0\6phase2$0$1^1+im8+nk0").   (* [comment removed for export] *)
Definition Ureg : ltac2:(zQ "40!oc!hlb!k5!ii1>6phase2$0@2$1$3$2") := ltac2:(zQ "a0!is5!oc!hm9!hrb!k5!ii1!isb!hsb!ihc!ire\6phase2$1@4$2$5$4@2$3$8$0@1$7@2$9@1$6^1$0").
Definition geomT_kn (phase2 : bool) : list kentry :=
  let '(U, Un) := Ureg phase2 in
  let H := SA vHDR 0 in let Hn := lit 144 in
  let A := SA vAUXV 0 in let An := lit 160 in
  [KDisj U Un H Hn; KDisj U Un A An; KDisj H Hn A An;
   KDisj H Hn (SA (lit 0) 0x10eb20) (lit 8); KDisj H Hn (SA (lit 0) 0x12ec38) (lit 8); KDisj H Hn (SA (lit 0) 0x12ee90) (lit 8);
   KDisj H Hn (SA (lit 0) 0x10000) (lit 0xe4000); KDisj H Hn (SA (lit 0) 0xfb9e0) (lit 0x1468);   (* [comment removed for export] *)
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
Definition LOCALS_OFF : ltac2:(zQ "20!oc!ma>6phase2$0$1") := ltac2:(zQ "30!oc!ma!ika\6phase2$0M0\6phase2$0$1^1@2$2-iq0+ig8+mn8").   (* [comment removed for export] *)
Definition stepframe_kn : ltac2:(zQ "30!oc!hl4!hn6>6phase2$0@1$1$2") := ltac2:(zQ "h40!hn6!hm2!hrb!ihc!oc!igc!hsb!ika!hr4!il6!is5!hn0!it1!ma!k5!it8!ih6!iu5!in7!ire\6phase2$4@3$1$0@3$8@2$2$3@2$7@1$5^1+ig0N8M4\6phase2$4$e^1@1$h1$c@1$6+hhhn7@3$1$0@3$8@2$2$3@2$7@1$5^1+ig8N8@1$6+vsuu8@3$1$0@3$8@2$2$3@2$7@1$5^1+ih0N8@2$h0$h2+m0@3$1$0@3$8@2$2$3@2$7@1$5^1+ih8N8@1$6M4\6phase2$4$d^1+tmis8+tlvt0@3$1$0@2$9@2$2$3$a@1$6@2$h3@2$7@1$5^1+ii0$a@3$1$0@2$9@2$2$3@1$f^1@1$6+l0@1$b$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cut1_T : ltac2:(zQ "30!oc!hl4!hn6>6phase2$0@1$1$2") := ltac2:(zQ "a0!ho4!hn6!oc!iua!iv4!jg0!jgb!jh6!jhf!ji8\6phase2$2@3$0$1@1$9^1@3$0$1@1$4^1@3$0$1@1$7^1@3$0$1$5@3$0$1$3@3$0$1$8@1$6^1").
Definition cut1_B : ltac2:(zQ "40!oc!hl4!hn6!io5>6phase2$0>acatchframe$0>2st$3@1$1$2") := ltac2:(zQ "60!oc!ho4!hn6!jj7!jk2!io5\6phase2$0\acatchframe$0\2st$5@3$1$2@1$3^1@3$4^3^2^1").
Definition cut1_kn : ltac2:(zQ "40!oc!hl4!hn6!io5>6phase2$0>acatchframe$0>2st$3@1$1$2") := ltac2:(zQ "60!oc!ho4!hn6!jkd!jl6!io5\6phase2$0\acatchframe$0\2st$5@3$1$2@1$4^3@3$3^3^2^1").

(* [comment removed for export] *)
Definition cut1_regs : ltac2:(zQ "30!oc!hl4!k5>6phase2$0@1$1$2") := ltac2:(zQ "h00!k5!hm2!kb!hsb!oc!ma!hn0!hh2!iu5!jlf!hh9!jm5!jmc!jn3!jn9!jnf\6phase2$4@3$1$0@1$3Z@3$1$0@1$3+tnvk4@3$1$0@1$9^1@3$1$0$a@3$1$0@1$3$7@3$1$0@1$2N5@3$1$0@1$2N6@3$1$0@1$2N7@3$1$0@1$8^1@3$1$0@1$3+hguri0@3$1$0@1$3+1@3$1$0@1$2N8@3$1$0@1$2N9@3$1$0@1$2Na@3$1$0@1$2Nb@3$1$0@1$2Nc@3$1$0@1$2Nd@3$1$0@1$2Ne@3$1$0@1$3M4\6phase2$4$5^1+1Z@3$1$0@1$3M4\6phase2$4$5^1+hjpm8+hhrs7@3$1$0@1$3M4\6phase2$4$5^1+hilv1+hihue@3$1$0$d@3$1$0@1$3+hhpi1@3$1$0@1$3+8@3$1$0$e@3$1$0$f@3$1$0$b@3$1$0$c@3$1$0@1$2Nf@3$1$0@1$2Nh0@3$1$0@1$2Nh1@3$1$0@1$2Nh2@1$6$0").

Definition cut1 : ltac2:(zQ "30!oc!jo5!io5>6phase2$0>acatchframe$0>2st$2$1") := ltac2:(zQ "a0!oc!jp0!hn0!jp7!ii1!jpc!jq4!jq9!jr3!io5\6phase2$0\acatchframe$0\2st$9@6$3+tnvk4@1$8^3@1$2$5@3$7^3^2^1$6@1$1$4").

(* [comment removed for export] *)
Definition PV : ltac2:(zQ "20!hl4!o6@1$0$1") := ltac2:(zQ "50!o6!ho4!jrf!hm2!hn0@3$1$0@2$2N5Nf@3$1$0@3$3$0Ni0@3$3$0Ni1@3$3$0Ni2@1$4$0@3$1$0@2$2Ni5Nhb@3$1$0@2$2Nk0Ni0@2$2Nm0Nb").                (* [comment removed for export] *)

(* [comment removed for export] *)
Definition CUT1_PC : Z := 0xd7f44.
Definition P1_HANDLER_FOUND : Z := 0xd6114.
Definition ends : ltac2:(zQ "40!oc!hl4!ma!io5>6phase2$0>2st$3@1$1$2") := ltac2:(zQ "a0!ma!oc!hm2!hn0!js6!hl4!jt0!jt8!io5!juc\6phase2$1\2st$8M1\6phase2$1@1$5$0^2M1\0$1@1$5$0@2$9@1$6^1Z@3$2$0$4@1$3$0@3$2$0$4@3$2$0@1$6^1@1$3$0@3$2$0$4@3$2$0$7@1$3$0").
End CUT.
(* [comment removed for export] *)
