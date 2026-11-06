(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat37Corelib7Numbers7BinNumshd1Z04bool46Stdlib6ZArith6BinInt1Zk03mulk06of_natk03powhd4Npos46Stdlib6NArith6BinNat1Nn43muln46of_natk03divk06modulo35stdpp9bitvectorbdefinitionsqa8bv_swrapqa2bv89OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX24FPX1~~~~~~t75ext_Zqa7Z_to_bvqabbv_unsigned04list37Corelib5Lists7ListDefhk16firstnhk15skipnk06to_nat3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehn4dbytes_le_to_Zt7ablob_bytes3h5LinuxProcessSemantics5Riscv5Instrhs15aluop05false04truehs15mulop3h5LinuxProcessSemantics5Riscv3Semig45alu64ig45low323h5LinuxProcessSemantics5Riscv7Preludeij84sextig45alu32ig47mul_divt77ext_val06optiont74expr04None04Somet76two64zk03lebk03sub04prod0acomparisont73lin03fst03snd04pairt74linst75snorm36Stdlib5Lists4Listiubafold_rightk03addt7clscale_termshs15M_MULt74ELitt73EMdk03eqbt76ltermshs17ALU_ADDt74EAlut7acoeffs_divt76lin_oft7blin_lowbitst76is_litt78shamt_oft75unlint74laddt76lscalet74zalut75EAluwt75zaluwt73zmdt74EMdwt74zmdwt74EExt04andb37Corelib4Init3Natju03add46Stdlib5Arith8PeanoNat3Natjv93eqbjv93lebt78zext_lit37Corelib4Init5Logickid1Ihk13nthij86bv_eqbt74ridxqa2BVqa4BvWft75saddrt72SAt79split_litt73env69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ko96v_addit76a_baset75a_offt76edenott78expr_eqbt78rangerel03orbt79RDisjointt77RInsidet78RPartialt78RUnknownt75two64k03maxk03mink07log2_upk03ltb79OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX2~~~~~~ll34exprll36kentryll38erange_fll3berange_fuel89OSSVerify6Proofsaboost_jsonafuzz_parse3lib8SymExec23SX24FPX2~~~~~~lrf6erangelrf8ctz_fuelll35saddrll35a_offll36a_basell38expr_eqblrfabase_rangelrfbkdisj_apartll34ELitlrfezbytes_le_to_Zhs17ALU_ANDll35mkAlull35two64lrf6ealignk04log2ll3acoeffs_divll33linll3blin_lowbitsll36lin_ofll35unlinlrfbor_disjoinths16ALU_ORll34EAlull36is_litll34zalull39lin_range04negbhs17ALU_SRLlrfaldiv_termslrfalin_nowrapll3blin_triviallrf5mkAndlrf4mkOrlrf5mkSrlll38shamt_ofhs15msizell38sidecond03nil04consll36SCFlatll34elenlrfawr_coveredll39SCStoreOkhs1bbranch_condig4cbranch_takenlrf7itv_ltu0aoption_maplrf7itv_ltslrfacond_on_eqlrfcrange_branchlrfalit_branchlrf7closedblrf8conc_trylrfbeval_closedlrf8subexprslrfaconcretizell38to_saddrll32SAll39split_litll39saddr_eqb03apphd8positivell34KImgll35KZeroll36SCDisjll3cranges_apart3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeou07Segment" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

Module SX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Inductive expr : Type :=
| ELit  (z : Z)                              (* [comment removed for export] *)
| EVar  (n : nat)                            (* [comment removed for export] *)
| EAlu  (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EAluw (op : aluop) (a b : expr)            (* [comment removed for export] *)
| EMd   (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EMdw  (op : mulop) (a b : expr)            (* [comment removed for export] *)
| EExt  (sx : bool) (lo n : nat) (e : expr)  (* [comment removed for export] *)
| EBlob (sx : bool) (k : nat) (i : Z) (n : nat).
                                             (* [comment removed for export] *)

(* [comment removed for export] *)
Record env : Type := Env { ev : nat -> word; eb : nat -> list byte }.

Definition ext_Z : ltac2:(zQ "30!h8!j6!ja>2sx$2>2lo$0>1n$0>1z$1$1") := ltac2:(zQ "c0!ja!j6!h8!l8!le!m7!md!oc!p2!pb!q1!s7\2sx$0\2lo$2\1n$2\1z$1=1u$1@2$a@2$9^1@2$5+2@2$3+8@1$4^3@2$5+2@2$3+8@1$4^2M0\2sx$0$1^5@2$b@2$7@1$6#8@1$8^3^1^1").

Definition ext_val : ltac2:(zQ "40!h8!md!t2!ja>2sx$3>2lo$0>1n$0>1v@1$2@1$1#k0@1$2@1$1#k0") := ltac2:(zQ "70!md!h8!ja!hhb!hi3!t2!hid\2sx$2\2lo$1\1n$1\1v@1$5@1$0#k0@2$4@1$0#k0@4$3^4^3^2@2$6@1$0#k0^1").

Definition blob_bytes : ltac2:(zQ "50!hjb!md!t2!h8!j6>2bs@1$0@1$2@1$1#8>1i$4>1n$3@1$0@1$2@1$1#8") := ltac2:(zQ "80!md!t2!hjb!h8!hl8!hm2!j6!hmb\2bs@1$2@1$1@1$0#8\1i$6\1n$3@3$4@1$1@1$0#8^1@3$5@1$1@1$0#8@1$7^2^3").

Definition blob_val : ltac2:(zQ "60!md!t2!ja!hjb!h8!j6>2sx$2>2bs@1$3@1$1@1$0#8>1i$5>1n$4@1$1@1$0#k0") := ltac2:(zQ "c0!ja!md!j6!hjb!h8!hq3!hr4!oc!p2!hi3!t2!s7\2sx$0\2bs@1$3@1$a@1$1#8\1i$2\1n$4@2$9@1$1#k0=1u$2@1$5@3$6^3^2^1M0\2sx$0$2^5@2$b@2$7@1$1#8@1$8^2^1^1").

Fixpoint edenot (E : env) (e : expr) : word :=
  match e with
  | ELit z => Z_to_bv 64 z
  | EVar n => ev E n
  | EAlu op a b => alu64 op (edenot E a) (edenot E b)
  | EAluw op a b => sext 64 (alu32 op (low32 (edenot E a)) (low32 (edenot E b)))
  | EMd op a b => mul_div op (edenot E a) (edenot E b)
  | EMdw op a b => sext 64 (mul_div op (low32 (edenot E a)) (low32 (edenot E b)))
  | EExt sx lo n a => ext_val sx lo n (edenot E a)
  | EBlob sx k i n => blob_val sx (eb E k) i n
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition aluop_eqb : ltac2:(zQ "20!hu5!ja>1a$0>1b$0$1") := ltac2:(zQ "40!hue!hu5!ja!hv5\1a$1\1b$1M1\1a$1$2^2M1\1b$1$2^1$3$0$0$0$0$0$0$0$0$0M1\1b$1$2^1$0$3$0$0$0$0$0$0$0$0M1\1b$1$2^1$0$0$3$0$0$0$0$0$0$0M1\1b$1$2^1$0$0$0$3$0$0$0$0$0$0M1\1b$1$2^1$0$0$0$0$3$0$0$0$0$0M1\1b$1$2^1$0$0$0$0$0$3$0$0$0$0M1\1b$1$2^1$0$0$0$0$0$0$3$0$0$0M1\1b$1$2^1$0$0$0$0$0$0$0$3$0$0M1\1b$1$2^1$0$0$0$0$0$0$0$0$3$0M1\1b$1$2^1$0$0$0$0$0$0$0$0$0$3").

Definition mulop_eqb : ltac2:(zQ "20!hvb!ja>1a$0>1b$0$1") := ltac2:(zQ "40!hue!hvb!ja!hv5\1a$1\1b$1M1\1a$1$2^2M1\1b$1$2^1$3$0$0$0$0$0$0$0M1\1b$1$2^1$0$3$0$0$0$0$0$0M1\1b$1$2^1$0$0$3$0$0$0$0$0M1\1b$1$2^1$0$0$0$3$0$0$0$0M1\1b$1$2^1$0$0$0$0$3$0$0$0M1\1b$1$2^1$0$0$0$0$0$3$0$0M1\1b$1$2^1$0$0$0$0$0$0$3$0M1\1b$1$2^1$0$0$0$0$0$0$0$3").

Fixpoint expr_eqb (x y : expr) : bool :=
  match x, y with
  | ELit a, ELit b => Z.eqb a b
  | EVar a, EVar b => Nat.eqb a b
  | EAlu o a b, EAlu o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EAluw o a b, EAluw o' a' b' => aluop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMd o a b, EMd o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EMdw o a b, EMdw o' a' b' => mulop_eqb o o' && expr_eqb a a' && expr_eqb b b'
  | EExt s l n a, EExt s' l' n' a' =>
      Bool.eqb s s' && Nat.eqb l l' && Nat.eqb n n' && expr_eqb a a'
  | EBlob s k i n, EBlob s' k' i' n' =>
      Bool.eqb s s' && Nat.eqb k k' && Z.eqb i i' && Nat.eqb n n'
  | _, _ => false
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zalu : ltac2:(zQ "20!j6!hu5>2op$1>1x$0>1y$0$0") := ltac2:(zQ "60!md!j6!hi3!hu5!ii6!hid\2op$3\1x$1\1y$1@2$5@1$0#k0@3$4^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition zaluw : ltac2:(zQ "20!j6!hu5>2op$1>1x$0>1y$0$0") := ltac2:(zQ "90!md!j6!iif!hi3!hu5!ile!im6!t2!hid\2op$4\1x$1\1y$1@2$8@1$0#k0Kd@3$5@1$0#i0@1$0#k0@3$6^3@1$2@2$3@1$0#k0^2@1$2@2$3@1$0#k0^1@1$7@1$0#k0").
Definition zmd : ltac2:(zQ "20!j6!hvb>2op$1>1x$0>1y$0$0") := ltac2:(zQ "60!md!j6!hi3!hvb!imf!hid\2op$3\1x$1\1y$1@2$5@1$0#k0@4$4@1$0#k0^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition zmdw : ltac2:(zQ "20!j6!hvb>2op$1>1x$0>1y$0$0") := ltac2:(zQ "90!md!j6!iif!hi3!hvb!ile!imf!t2!hid\2op$4\1x$1\1y$1@2$8@1$0#k0Kd@3$5@1$0#i0@1$0#k0@4$6@1$0#i0^3@1$2@2$3@1$0#k0^2@1$2@2$3@1$0#k0^1@1$7@1$0#k0").
Definition zext_lit : ltac2:(zQ "30!h8!j6!ja>2sx$2>2lo$0>1n$0>1x$1$1") := ltac2:(zQ "70!h8!md!ja!j6!ina!hi3!hid\2sx$2\2lo$0\1n$0\1x$3@2$6@1$1#k0@4$4^4^3^2@2$5@1$1#k0^1").

Definition is_lit : ltac2:(zQ "30!io4!j6!ioc>1e$2@1$0$1") := ltac2:(zQ "90!ioc!j6!ip3!h8!ja!hu5!hvb!ip9!io4\1e$0M0\1e$0@1$8$1^1\1z$1@2$7$1^1\1n$3@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2sx$4\2lo$3\1n$3\2e0$0@1$2$1\2sx$4\1k$3\1i$1\1n$3@1$2$1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition two64z : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!m7@2$0+2+k0").
Definition snorm : ltac2:(zQ "10!j6>1k$0$0") := ltac2:(zQ "70!j6!ja!ipf!iq8!q1!m7!iqe\1k$0=1m$0@2$4^1$2M1\0$1$0@2$3@2$5+2+jf^1@2$6^1$2^1").

Definition lin : ltac2:(zQ "00T") := ltac2:(zQ "40!ir4!j6!hjb!ioc@2$0$1@1$2@2$0$1$3").

Definition ctor_ix : ltac2:(zQ "20!h8!ioc>1e$1$0") := ltac2:(zQ "60!ioc!h8!ja!j6!hu5!hvb\1e$0M0\1e$0$1^1\1z$3N0\1n$1N1\2op$4\1a$0\1b$0N2\2op$4\1a$0\1b$0N3\2op$5\1a$0\1b$0N4\2op$5\1a$0\1b$0N5\2sx$2\2lo$1\1n$1\2e0$0N6\2sx$2\1k$1\1i$3\1n$1N7").
Definition aluop_ix : ltac2:(zQ "20!h8!hu5>2op$1$0") := ltac2:(zQ "20!hu5!h8\2op$0M0\2op$0$1^1N0N1N2N3N4N5N6N7N8N9").
Definition mulop_ix : ltac2:(zQ "20!h8!hvb>2op$1$0") := ltac2:(zQ "20!hvb!h8\2op$0M0\2op$0$1^1N0N1N2N3N4N5N6N7").
Definition bool_ix : ltac2:(zQ "20!ja!h8>1b$0$1") := ltac2:(zQ "20!ja!h8\1b$0M0\1b$0$1^1N1N0").
Definition lexc : ltac2:(zQ "10!ira>1c$0>1k$0$0") := ltac2:(zQ "10!ira\1c$0\1k$0M0\1c$0$0^2^1^2^2").

Fixpoint expr_cmp (x y : expr) {struct x} : comparison :=
  match x, y with
  | ELit a, ELit b => Z.compare a b
  | EVar a, EVar b => Nat.compare a b
  | EAlu o a b, EAlu o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EAluw o a b, EAluw o' a' b' =>
      lexc (Nat.compare (aluop_ix o) (aluop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMd o a b, EMd o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EMdw o a b, EMdw o' a' b' =>
      lexc (Nat.compare (mulop_ix o) (mulop_ix o')) (lexc (expr_cmp a a') (expr_cmp b b'))
  | EExt s l n e, EExt s' l' n' e' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare l l') (lexc (Nat.compare n n') (expr_cmp e e')))
  | EBlob s k i n, EBlob s' k' i' n' =>
      lexc (Nat.compare (bool_ix s) (bool_ix s'))
           (lexc (Nat.compare k k') (lexc (Z.compare i i') (Nat.compare n n')))
  | _, _ => Nat.compare (ctor_ix x) (ctor_ix y)
  end.

(* [comment removed for export] *)
Fixpoint lins (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb (snorm k) 0 then [] else [(snorm k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then
        (let s := snorm (k + k') in if Z.eqb s 0 then rest else (s, a') :: rest)
      else match expr_cmp a a' with
           | Lt => if Z.eqb (snorm k) 0 then ts else (snorm k, a) :: ts
           | _ => (k', a') :: lins k a rest
           end
  end.

Definition ladd : ltac2:(zQ "10!is6>1x$0>1y$0$0") := ltac2:(zQ "c0!j6!ioc!ir4!hjb!isc!it1!is6!it6!itc!iu3!ive!jgc\1x$6\1y$6@4$7$0@1$3@2$2$0$1@1$9@2$b@3$4$0@1$3@2$2$0$1^2@3$4$0@1$3@2$2$0$1^1@5$a@1$3@2$2$0$1@2$2$0$1\1t@2$2$0$1\3acc@1$3@2$2$0$1@3$8@3$4$0$1^2@3$5$0$1^2^1@3$5$0@1$3@2$2$0$1^1@3$5$0@1$3@2$2$0$1^2").

Fixpoint lscale_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest =>
      let k' := snorm (m * k) in
      if Z.eqb k' 0 then lscale_terms m rest else (k', a) :: lscale_terms m rest
  end.

Definition lscale : ltac2:(zQ "20!is6!j6>1m$1>1x$0$0") := ltac2:(zQ "b0!j6!hjb!ir4!ioc!isc!it6!it1!is6!jh2!iu3!l8\1m$0\1x$7@4$5$0@1$1@2$2$0$3@1$9@2$a^2@3$4$0@1$1@2$2$0$3^1@2$8^2@3$6$0@1$1@2$2$0$3^1").

(* [comment removed for export] *)
Fixpoint lin_of (e : expr) : lin :=
  match e with
  | ELit z => (snorm z, [])
  | EAlu ALU_ADD a b => ladd (lin_of a) (lin_of b)
  | EAlu ALU_SUB a b => ladd (lin_of a) (lscale (-1) (lin_of b))
  | EAlu ALU_SLL a (ELit s) => lscale (2 ^ (s mod 64)) (lin_of a)
  | EMd M_MUL (ELit k) a => lscale k (lin_of a)
  | EMd M_MUL a (ELit k) => lscale k (lin_of a)
  | _ => (0%Z, [(1%Z, e)])
  end.

Definition lterm : ltac2:(zQ "30!ioc!ir4!j6>1t@2$1$2$0$0") := ltac2:(zQ "a0!ioc!j6!ja!isc!it1!ir4!ji1!jia!jj1!jj7\1t@2$5$1$0M2\0$2$0@2$9@3$3$1$0^1+1@3$4$1$0^1@3$8$6@1$7@3$3$1$0^1@3$4$1$0^1").

Fixpoint lterms (ts : list (Z * expr)) : expr :=
  match ts with
  | [] => ELit 0
  | [t] => lterm t
  | t :: rest => EAlu ALU_ADD (lterm t) (lterms rest)
  end.

Definition unlin : ltac2:(zQ "20!ioc!is6>1x$1$0") := ltac2:(zQ "d1!j6!ioc!hjb!ir4!isc!it1!ja!jia!jjd!jk6!jl1!is6!jj7&@1$8@3$5$0@1$2@2$3$0$1^3\1x$bM2\1x@1$2@2$3$0$1$1@3$5$0@1$2@2$3$0$1^1@1$7@3$4$0@1$2@2$3$0$1^1\1p@2$3$0$1\1l@1$2@2$3$0$1M6\0$6$1@2$c@3$4$0@1$2@2$3$0$1^3Z~0@3$a$9~0@1$7@3$4$0@1$2@2$3$0$1^3").

(* [comment removed for export] *)
Fixpoint coeffs_div (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, _) :: rest => (Z.eqb (k mod m) 0 && coeffs_div m rest)%bool
  end.

Definition lin_lowbits : ltac2:(zQ "30!j6!io4!ioc>1e$2>1k$0@1$1$0") := ltac2:(zQ "f0!j6!ioc!ja!hjb!ir4!m7!ip3!ip9!isc!io4!it1!jl8!is6!jm5!q1\1e$1\1k$0=1l$c@1$d^2M2\0$2@1$9$0@2$b@2$5+2^2@3$a$0@1$3@2$4$0$1^1@2$7$0@2$e@3$8$0@1$3@2$4$0$1^1@2$5+2^2@1$6$0").

(* [comment removed for export] *)
Definition shamt_of : ltac2:(zQ "30!j6!io4!ioc>1e$2>4bits$0@1$1$0") := ltac2:(zQ "b2!ioc!jme!h8!j6!ja!hu5!hvb!ip9!io4!q1!m7&\2op$5\1a$0\1b$0@2$1^5^4&\2op$6\1a$0\1b$0@2$1^5^4\1e$0\4bits$3M0\1e$0@1$8$3^2\1s$3@2$7$3@2$9^1@2$a+2^2\1n$2@2$1^3^2~0~0~1~1\2sx$4\2lo$2\1n$2\2e0$0@2$1^6^5\2sx$4\1k$2\1i$3\1n$2@2$1^6^5").

Definition mkAlu : ltac2:(zQ "20!ioc!hu5>2op$1>1a$0>1b$0$0") := ltac2:(zQ "e4!io4!j6!jl1!ioc!jm5!jnc!jo5!jp0!hu5!jia!jp8!jpf!m7!jq8&M0\1x@1$0$1$3@2$6^2+6\1s$1@3$2^5^4@1$9^1@3$2^4^3^2&M0\1x@1$0$1$3@1$5^2\1z$1@3$2^5^4^3~0&M0\1x@1$0$1$3@2$6^1+6\1s$1@3$2^4^3@1$9^1@3$2^3^2^1&M0\1x@1$0$1$3@1$5^1\1z$1@3$2^4^3^2~2\2op$8\1a$3\1b$3M0\1x@1$0$1$3@1$5^2\1x$1M0\1x@1$0$1$3@1$5^2\1y$1@1$9@3$d^5^2^1M8\2op$8$3^4@1$7@2$a@1$4^3@1$4^2@1$7@2$a@1$4^3@2$b-1@1$4^2M0\1x@1$0$1$3@2$6^2+6\1s$1@1$7@2$b@2$c+2^1@1$4^4@3$2^4^3^2@3$2^4^3^2@3$2^4^3^2@3$2^4^3^2~1~1@3$2^4^3^2@3$2^4^3^2M8\2op$8$3^3@1$7@2$a@1$4^2@1$4^1@1$7@2$a@1$4^2@2$b-1@1$4^1M0\1x@1$0$1$3@2$6^1+6\1s$1@1$7@2$b@2$c+2^1@1$4^3@3$2^3^2^1@3$2^3^2^1@3$2^3^2^1@3$2^3^2^1~3~3@3$2^3^2^1@3$2^3^2^1").

Definition mkAluw : ltac2:(zQ "20!ioc!hu5>2op$1>1a$0>1b$0$0") := ltac2:(zQ "98!io4!j6!jqf!ioc!jnc!jia!jr7!jo5!hu5&M0\1x@1$0$1$3@1$4^4\1x$1@1$5@3$6^6^1^2@3$2^5^4@1$5^1&\1s$1~0&M0\1x@1$0$1$3@2$7^2+5~1@3$2^4^3^2&M0\1x@1$0$1$3@1$4^2\1z$1@3$2^5^4^3~2&M0\1x@1$0$1$3@1$4^3\1x$1@1$5@3$6^5^1^2@3$2^4^3@1$5^1&\1s$1~4&M0\1x@1$0$1$3@2$7^1+5~5@3$2^3^2^1&M0\1x@1$0$1$3@1$4^1\1z$1@3$2^4^3^2~6\2op$8\1a$3\1b$3M0\1x@1$0$1$3@1$4^2\1x$1M0\1x@1$0$1$3@1$4^2\1y$1@1$5@3$6^5^2^1M8\2op$8$3^4@3$2^4^3^2@3$2^4^3^2~3@3$2^4^3^2@3$2^4^3^2@3$2^4^3^2~3~3@3$2^4^3^2@3$2^4^3^2M8\2op$8$3^3@3$2^3^2^1@3$2^3^2^1~7@3$2^3^2^1@3$2^3^2^1@3$2^3^2^1~7~7@3$2^3^2^1@3$2^3^2^1").

Definition mkMd : ltac2:(zQ "20!ioc!hvb>2op$1>1a$0>1b$0$0") := ltac2:(zQ "b0!jj1!ioc!io4!j6!hvb!jnc!jm5!jpf!jp0!jia!jrf\2op$4\1a$1\1b$1M2\1x@1$2$3$1@1$5^2\1x$3M2\1x@1$2$3$1@1$5^2\1y$3@1$9@3$a^5^2^1M4\2op$4$1^4@1$8@2$7^1@1$6^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2M2\1x@1$2$3$1@1$5^1\1y$3M4\2op$4$1^4@1$8@2$7^1@1$6^3@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^3^2^1").

Definition mkMdw : ltac2:(zQ "20!ioc!hvb>2op$1>1a$0>1b$0$0") := ltac2:(zQ "80!io4!j6!ioc!js5!jnc!hvb!jia!jsc\2op$5\1a$2\1b$2M0\1x@1$0$1$2@1$4^2\1x$1M0\1x@1$0$1$2@1$4^2\1y$1@1$6@3$7^5^2^1@3$3^4^3^2@3$3^3^2^1").

(* [comment removed for export] *)
Definition mkExt : ltac2:(zQ "30!h8!ioc!ja>2sx$2>2lo$0>1n$0>1e$1$1") := ltac2:(zQ "di0!ioc!jt3!ja!h8!j6!hu5!hvb!jta!jv2!kh4!khb!jia!ki2&\2op$5\1a$0\1b$0@4$1^8^7^6^5&\2op$6\1a$0\1b$0@4$1^8^7^6^5&\2op$5\1a$0\1b$0@4$1^a^9^8^7&\2op$6\1a$0\1b$0@4$1^a^9^8^7&@2$7@2$a@2$8^a^9^2@2$a^2N8&M2\0$2$0~4@4$1^b@2$8^3^a^9^1@4$1^b^a^9^8&M2\3sx0$2$0^4@4$1^b^a^9^8~5&\2e'$0~6&\2n'$3~7&\3lo'$3~8&\3sx0$2~9&\1k$3\1i$4\2n0$3@4$1^b^a^9^8&\3sx0$2~b&M0\1e$0$0^4\1z$4@4$1^8^7^6^5\2n0$3@4$1^8^7^6^5~2~2~3~3~a~c&M2\0$2$0@2$7@2$9^6N0@2$9^5N8^4~d&\1b$0~e&\1a$0~f&\2op$5~h0&\2op$6~h0&\2op$5\1a$0\1b$0@4$1^b^a^9^8&\2op$6\1a$0\1b$0@4$1^b^a^9^8&@2$7@2$a@2$8^b^a^2@2$a^2N8&M2\0$2$0~h5@4$1^c@2$8^3^b^a^1@4$1^c^b^a^9&M2\3sx0$2$0^4@4$1^c^b^a^9~h6&\2e'$0~h7&\2n'$3~h8&\3lo'$3~h9&\3sx0$2~ha&\1k$3\1i$4\2n0$3@4$1^c^b^a^9&\3sx0$2~hc&M0\1e$0$0^5\1z$4@4$1^9^8^7^6\2n0$3@4$1^9^8^7^6~h3~h3~h4~h4~hb~hd&M2\0$2$0@2$7@2$9^7N0@2$9^6N8^5~he\2sx$2\2lo$3\1n$3\1e$0M0\1e$0$0^1\1x$4@1$b@4$c^5^4^3^1\2n0$3M2\0$2$0@2$7@2$9^4N0@2$9^3N8^2M0\1e$0$0^2\1z$4@4$1^6^5^4^3\2n0$3@4$1^6^5^4^3~0~0~1~1\3sx0$2\3lo'$3\2n'$3\2e'$0M2\3sx0$2$0^4@4$1^9^8^7^6M2\0$2$0@2$7@2$a@2$8^8^7^2@2$a^2N8@4$1^9@2$8^3^8^7^1@4$1^9^8^7^6\3sx0$2\1k$3\1i$4\2n0$3@4$1^9^8^7^6~h1~h1~h2~h2\3sx0$2\3lo0$3\2n0$3\2e0$0~hf\3sx0$2\1k$3\1i$4\2n0$3~hf").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ridx : ltac2:(zQ "30!h8!md!t2>1r@1$2@1$1#5$0") := ltac2:(zQ "40!md!hmb!t2!hid\1r@1$2@1$0#5@1$1@2$3@1$0#5^1").

Definition sr_get : ltac2:(zQ "40!ioc!hjb!md!t2>2sr@1$1$0>1r@1$3@1$2#5$0") := ltac2:(zQ "c0!md!ioc!ja!jia!hjb!kk1!kk6!kkd!kl7!kle!km3!t2\2sr@1$4$1\1r@1$b@1$0#5M2\0$2$1@3$7@1$0#5^1@3$9@1$0#5ZKv$5@2$a@1$0#5Z@1$3Z@4$6$1@1$8^1^2@1$3Z").

Fixpoint sr_upd (sr : list expr) (n : nat) (e : expr) : list expr :=
  match n with
  | O => match sr with [] => [e] | _ :: t => e :: t end
  | S n' => match sr with
            | [] => ELit 0 :: sr_upd [] n' e
            | h :: t => h :: sr_upd t n' e
            end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record saddr : Type := SA { a_base : expr; a_off : Z }.

Definition split_lit : ltac2:(zQ "30!ioc!ir4!j6>1e$0@2$1$0$2") := ltac2:(zQ "93!ioc!j6!it6!h8!hu5!ja!hvb!ir4!jia&\3op0$4\1a$0\2b1$0@4$2$0$1^7Z&\3op0$6\1a$0\2b1$0@4$2$0$1^7Z&\2op$6\1a$0\1b$0@4$2$0$1^4Z\1e$0M0\1e$0@2$7$0$1^1\1z$1@4$2$0$1@1$8Z^1\1n$3@4$2$0$1^2Z\2op$4\1b$0\2b0$0M4\2op$4@2$7$0$1^3M0\2b0$0@2$7$0$1^1\1z$1@4$2$0$1^3^1\1n$3@4$2$0$1^5Z~0~0~1~1\2sx$5\2lo$3\1n$3\2e0$0@4$2$0$1^8Z\2sx$5\1k$3\1i$1\1n$3@4$2$0$1^8Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z\2op$4\1a$0\1b$0@4$2$0$1^4Z~2~2\2sx$5\2lo$3\1n$3\2e0$0@4$2$0$1^5Z\2sx$5\1k$3\1i$1\1n$3@4$2$0$1^5Z").

Definition to_saddr : ltac2:(zQ "30!j6!ioc!kma>1e$1>3imm$0$2") := ltac2:(zQ "70!j6!ioc!ir4!kn2!kma!kn7!jgc\1e$1\3imm$0M2\1p@2$2$1$0$4@1$5^2\1b$1\1k$0@2$3^2@2$6^1^3").

Definition adenot : ltac2:(zQ "40!md!ko3!kma!t2>1E$1>1a$2@1$3@1$0#k0") := ltac2:(zQ "60!ks4!kse!kt7!ktf!ko3!kma\1E$4\1a$5@2$0@2$3^2@1$1^1@1$2^1").

Definition saddr_eqb : ltac2:(zQ "20!kma!ja>1a$0>1b$0$1") := ltac2:(zQ "60!kse!kt7!kma!jta!ku8!jj7\1a$2\1b$2@2$3@2$4@1$0^2@1$0^1@2$5@1$1^2@1$1^1").

(* [comment removed for export] *)
Record sentry : Type := SE { e_addr : saddr; e_width : nat; e_val : expr }.

(* [comment removed for export] *)
Inductive kentry : Type :=
| KWord (a : saddr) (w : nat) (v : expr)      (* [comment removed for export] *)
| KZero (a : saddr) (n : expr)                (* [comment removed for export] *)
| KBlob (a : saddr) (n : expr) (k : nat)      (* [comment removed for export] *)
| KImg  (lo hi : Z)                           (* [comment removed for export] *)
| KAlign (e : expr) (m : Z)                   (* [comment removed for export] *)
| KRange (e : expr) (lo hi : Z)               (* [comment removed for export] *)
| KWr (a : saddr) (n : Z)                     (* [comment removed for export] *)
| KDisj (a1 : saddr) (n1 : Z) (a2 : saddr) (n2 : Z).
                                              (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : expr)                     (* [comment removed for export] *)
| SCDisj     (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCInside   (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCStoreOk  (a : saddr) (n : nat)                      (* [comment removed for export] *)
| SCReadBase (a : saddr) (n : nat) (sx : bool) (e : expr)  (* [comment removed for export] *)
| SCEq       (a b : expr).                              (* [comment removed for export] *)

Record sym_state : Type := SS {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;       (* [comment removed for export] *)
  s_know : list kentry;
  s_next : nat                (* [comment removed for export] *)
}.

Definition sset (ss : sym_state) (rd : reg) (e : expr) (npc : Z) : sym_state :=
  SS npc (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) e)
     (s_log ss) (s_know ss) (s_next ss).

Definition sjump (ss : sym_state) (npc : Z) : sym_state :=
  SS npc (s_regs ss) (s_log ss) (s_know ss) (s_next ss).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rangerel := RInside (delta : Z) | RDisjoint | RPartial | RUnknown.

(* [comment removed for export] *)
Definition rel_lit : ltac2:(zQ "30!j6!ioc!kv3>2rb$1>2rk$0>2rn$0>2kb$1>2kk$0>2kn$0$2") := ltac2:(zQ "e0!ja!j6!jgc!iq8!kv3!ioc!jta!kve!lg3!lgf!lh9!li4!ku8!iqe\2rb$5\2rk$1\2rn$1\2kb$5\2kk$1\2kn$1M0\0$0$4@2$c^6^3M0\0$0$4@2$6@2$3^2^5@2$3@2$2^5^4@2$2^2^1@1$9@2$d^5^2M0\0$0$4@2$7@2$3@2$2^5^4^2@2$3@2$2^2^1^5$8$a$b").

Definition elen : ltac2:(zQ "20!h8!ioc>1n$0$1") := ltac2:(zQ "30!h8!jia!le\1n$0@1$1@1$2^1").

(* [comment removed for export] *)
Fixpoint find_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest => if expr_eqb e e' then Some (lo, hi) else find_range rest e
  | _ :: rest => find_range rest e
  end.

(* [comment removed for export] *)
Fixpoint find_align (kn : list kentry) (e : expr) : option Z :=
  match kn with
  | [] => None
  | KAlign e' m :: rest => if expr_eqb e e' then Some m else find_align rest e
  | _ :: rest => find_align rest e
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition two64 : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!m7@2$0+2+k0").

Definition clampi : ltac2:(zQ "20!j6!ir4>1r@2$1$0$0@2$1$0$0") := ltac2:(zQ "70!j6!ir4!it6!lif!lj7!ljd!iqe\1r@2$1$0$0M1\1r@2$1$0$0@2$1$0$0^1\2lo$0\2hi$0@4$2$0$0@2$4^2Z@2$5^1@2$6$3+1").

(* [comment removed for export] *)
Definition mask_cover : ltac2:(zQ "10!j6>1h$0$0") := ltac2:(zQ "70!ja!j6!jgc!lk3!lkd!m7!iqe\1h$1M0\0$0$1@2$4^1ZZ@2$6@2$5+2@1$3@2$2^1+1+1").

Definition lit_shamt : ltac2:(zQ "30!io4!j6!ioc>1e$2@1$0$1") := ltac2:(zQ "a0!ioc!j6!ip3!h8!ja!hu5!hvb!ip9!io4!q1\1e$0M0\1e$0@1$8$1^1\1s$1@2$7$1@2$9^1+k0\1n$3@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2sx$4\2lo$3\1n$3\2e0$0@1$2$1\2sx$4\1k$3\1i$1\1n$3@1$2$1").

(* [comment removed for export] *)
Definition zsigned64 : ltac2:(zQ "10!j6>1v$0$0") := ltac2:(zQ "60!ja!j6!lif!iq8!m7!iqe\1v$1M0\0$0$1@2$3@2$4+2+jf^1@2$5^1$2^1").

(* [comment removed for export] *)
Fixpoint lin_range (rng : expr -> option (Z * Z)) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  match ts with
  | [] => Some (c, c)
  | (k, a) :: rest =>
      match rng a, lin_range rng c rest with
      | Some (al, ah), Some (lo, hi) =>
          if Z.leb 0 k then Some ((lo + k * al)%Z, (hi + k * ah)%Z)
          else Some ((lo + k * ah)%Z, (hi + k * al)%Z)
      | _, _ => None
      end
  end.

Definition lin_trivial : ltac2:(zQ "20!ja!is6>1l$1$0") := ltac2:(zQ "90!ir4!j6!ioc!hjb!ja!hue!jj7!jta!is6\1l$8M0\1l@2$0$1@1$3@2$0$1$2$4^1\1c$1\2l0@1$3@2$0$1$2M3\2l0@1$3@2$0$1$2$4^1$5\1p@2$0$1$2\2l1@1$3@2$0$1$2M0\1p@2$0$1$2$4^2\1k$1\1e$2M3\2l1@1$3@2$0$1$2$4^3@2$7@2$6^6Z@2$6^2+1\2p0@2$0$1$2\2l2@1$3@2$0$1$2$5").

Fixpoint erange_f (fuel : nat) (kn : list kentry) (e : expr) {struct fuel} : option (Z * Z) :=
  match fuel with
  | O => None
  | S fuel' =>
  let erange := erange_f fuel' in
  match find_range kn e with
  | Some r => Some (clampi r)
  | None =>
  match (let l := lin_of e in
         if lin_trivial l then None
         else match lin_range (erange kn) (fst l) (snd l) with
              | Some (lo, hi) => if (Z.leb 0 lo && Z.ltb hi two64)%bool then Some (lo, hi) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := (z mod two64)%Z in Some (v, v)
  | EVar _ => None
  | EAlu op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb (ah + bh) two64 then Some ((al + bl)%Z, (ah + bh)%Z)
              else if Z.leb two64 (al + bl) then Some ((al + bl - two64)%Z, (ah + bh - two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.leb bh al then Some ((al - bh)%Z, (ah - bl)%Z)
              else if Z.ltb ah bl then Some ((al - bh + two64)%Z, (ah - bl + two64)%Z)
              else None
          | _, _ => None
          end
      | ALU_AND =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
      | ALU_OR =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) => Some (Z.max al bl, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_XOR =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, mask_cover (Z.max ah bh))
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s => Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z)
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb ah (2 ^ 63) then Some ((al / 2 ^ s)%Z, (ah / 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              if Z.ltb (ah * 2 ^ s) two64 then Some ((al * 2 ^ s)%Z, (ah * 2 ^ s)%Z) else None
          | _, _ => None
          end
      | ALU_SLTU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if Z.ltb ah bl then Some (1%Z, 1%Z)
              else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      | ALU_SLT =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.ltb ah (2 ^ 63) && Z.ltb bh (2 ^ 63))%bool then
                (if Z.ltb ah bl then Some (1%Z, 1%Z)
                 else if Z.leb bh al then Some (0%Z, 0%Z) else Some (0%Z, 1%Z))
              else Some (0%Z, 1%Z)
          | _, _ => Some (0%Z, 1%Z)
          end
      end
  | EAluw op a b =>
      match op with
      | ALU_ADD =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              let bl' := if Z.eqb bl bh then zsigned64 bl else bl in
              let bh' := if Z.eqb bl bh then zsigned64 bh else bh in
              if (Z.leb 0 (al + bl') && Z.ltb (ah + bh') (2 ^ 31))%bool
              then Some ((al + bl')%Z, (ah + bh')%Z) else None
          | _, _ => None
          end
      | ALU_SUB =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb bh al && Z.ltb (ah - bl) (2 ^ 31))%bool
              then Some ((al - bh)%Z, (ah - bl)%Z) else None
          | _, _ => None
          end
      | ALU_SLL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb (ah * 2 ^ s') (2 ^ 31) then Some ((al * 2 ^ s')%Z, (ah * 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRL =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if (Z.ltb ah (2 ^ 32) && (Z.ltb 0 s' || Z.ltb ah (2 ^ 31)))%bool
              then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | ALU_SRA =>
          match erange kn a, lit_shamt b with
          | Some (al, ah), Some s =>
              let s' := (s mod 32)%Z in
              if Z.ltb ah (2 ^ 31) then Some ((al / 2 ^ s')%Z, (ah / 2 ^ s')%Z) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMd op a b =>
      match op with
      | M_MUL =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl && Z.ltb (ah * bh) two64)%bool
              then Some ((al * bl)%Z, (ah * bh)%Z) else None
          | _, _ => None
          end
      | M_MULHU =>
          match erange kn a, erange kn b with
          | Some (al, ah), Some (bl, bh) =>
              if (Z.leb 0 al && Z.leb 0 bl)%bool
              then Some ((al * bl / two64)%Z, (ah * bh / two64)%Z) else None
          | _, _ => None
          end
      | M_DIVU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some ((al / d')%Z, (ah / d')%Z) else None
          | _, _ => None
          end
      | M_REMU =>
          match erange kn a, b with
          | Some (al, ah), ELit d =>
              let d' := (d mod two64)%Z in
              if Z.ltb 0 d' then Some (0%Z, Z.min ah (d' - 1)) else None
          | _, _ => None
          end
      | _ => None
      end
  | EMdw _ _ _ => None
  | EExt sx lo n a =>
      let w := (2 ^ (8 * Z.of_nat n))%Z in
      if sx then
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah) else None
        | _, _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      if sx then None else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.

(* [comment removed for export] *)
Definition erange_fuel : nat := 64%nat.
End FPX1.
Global Opaque erange_fuel.
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition erange : ltac2:(zQ "60!j6!hjb!io4!ir4!lp2!lpa>2kn@1$1$5>1e$4@1$2@2$3$0$0") := ltac2:(zQ "50!hjb!lq4!lr0!lp2!lpa\2kn@1$0$4\1e$3@3$1$2^2^1").


Definition base_range : ltac2:(zQ "60!j6!hjb!io4!ir4!lp2!lpa>2kn@1$1$5>1e$4@1$2@2$3$0$0") := ltac2:(zQ "40!hjb!mg3!lp2!lpa\2kn@1$0$3\1e$2@2$1^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ctz_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if (Z.eqb (z mod 2) 0)%Z then (1 + ctz_fuel f (z / 2))%Z else 0%Z
  end.
Definition ctz64 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "20!j6!mgd\1z$0@2$1Nk0^1").

(* [comment removed for export] *)
Fixpoint ealign (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (z mod two64)
  | EAlu ALU_ADD a b => Z.min (ealign kn a) (ealign kn b)
  | EAlu ALU_SUB a b => Z.min (ealign kn a) (ealign kn b)
  | EAlu ALU_AND a b => Z.max (ealign kn a) (ealign kn b)
  | EAlu ALU_OR a b => Z.min (ealign kn a) (ealign kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign kn a + ealign kn b)%Z 64
  | _ => 0%Z
  end
  end.

(* [comment removed for export] *)
Definition sub_itv : ltac2:(zQ "40!j6!ja!lp2!mh9>1b$2>1k$0>1n$0>1c$3>1m$0$1") := ltac2:(zQ "90!j6!jta!mi2!jgc!iq8!mib!lp2!mj5!mh9\1b$6\1k$0\1n$0\1c$8\1m$0@2$1@2$1@2$7^5@1$5^2@2$4@1$2^2^4@2$4@2$3^4^3@2$3@1$2^2^1").

(* [comment removed for export] *)
Fixpoint kdisj_apart (kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      ((sub_itv b1 k1 n1 c1 m1 && sub_itv b2 k2 n2 c2 m2)
       || (sub_itv b1 k1 n1 c2 m2 && sub_itv b2 k2 n2 c1 m1)
       || kdisj_apart rest b1 k1 n1 b2 k2 n2)%bool
  | _ :: rest => kdisj_apart rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apart : ltac2:(zQ "50!j6!lp2!ja!hjb!lpa>2kn@1$3$4>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2") := ltac2:(zQ "d0!j6!ir4!jgc!ja!io4!hue!kve!mk1!lp2!iq8!hjb!mkf!lpa\2kn@1$a$c\2b1$8\2k1$0\2n1$0\2b2$8\2k2$0\2n2$0@2$6M4\1x@1$4@2$1$0$0$3@2$7^7^6\1p@2$1$0$0M1\1p@2$1$0$0$3^1\3lo1$0\3hi1$0M4\1x@1$4@2$1$0$0$3@2$7^a^6\2p0@2$1$0$0M1\2p0@2$1$0$0$3^1\3lo2$0\3hi2$0@2$6@2$9@2$2@2$2^4^b^a@2$2^2^8@2$9@2$2@2$2^1^8^7@2$2^5^b$5$5@7$b^7^6^5^4^3^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lres :=
| LHit (v : expr) (scs : list sidecond) (hints : list bool)
| LMiss (scs : list sidecond) (hints : list bool)     (* [comment removed for export] *)
| LStuck.

(* [comment removed for export] *)
Fixpoint log_lookup (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookup kn rest rb rk n sx hints acc
      | RPartial => LStuck
      | RUnknown =>
          if ranges_apart kn rb rk (Z.of_nat n) kb kk (Z.of_nat w)
          then log_lookup kn rest rb rk n sx hints acc
          else
          match hints with
          | false :: _ => LStuck
          | _ => log_lookup kn rest rb rk n sx (tl hints)
                   (SCDisj (SA rb rk) (elen n) (SA kb kk) (elen w) :: acc)
          end
      end
  end.

(* [comment removed for export] *)
Fixpoint img_bytes (segs : list Segment) (a : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' =>
      match seg_rom segs (Z_to_bv 64 a) with
      | Some b => match img_bytes segs (a + 1) n' with
                  | Some r => Some (bv_unsigned b :: r)
                  | None => None
                  end
      | None => None
      end
  end.

Fixpoint zbytes_le_to_Z (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor b (Z.shiftl (zbytes_le_to_Z rest) 8)
  end.

Definition lit_of_bytes : ltac2:(zQ "50!ja!hjb!h8!j6!lp2>2sx$0>1n$2>2bs@1$1$3$4") := ltac2:(zQ "a0!ja!j6!hjb!h8!md!mle!mm6!oc!p2!s7\2sx$0\1n$3\2bs@1$2$1@1$5=1u$1@1$6^1M0\2sx$0$1^4@2$9@2$7@1$4#8@1$8^3^1^1").

(* [comment removed for export] *)
Fixpoint know_lookup (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  match kn with
  | [] => LMiss acc hints
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w v =>
          match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
          | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KZero (SA kb kk) len =>
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit (ELit 0) acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KBlob (SA kb kk) len k =>
          if expr_eqb rb kb then
            (* [comment removed for export] *)
            if Z.leb kk rk then
              match len with
              | ELit l0 =>
                  if Z.leb (rk + Z.of_nat n) (kk + (l0 mod 2^64)%Z)
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else if Z.leb (kk + (l0 mod 2^64)%Z) rk then know_lookup segs rest rb rk n sx hints acc
                  else LStuck
              | _ =>
                  match hints with
                  | true :: hs => LHit (EBlob sx k (rk - kk) n)
                                    (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
            else know_lookup segs rest rb rk n sx hints acc
          else know_lookup segs rest rb rk n sx hints acc
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.leb (rk + Z.of_nat n) hi)%bool then
                match img_bytes segs rk n with
                | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                | None => LStuck
                end
              else know_lookup segs rest rb rk n sx hints acc
          | _ => know_lookup segs rest rb rk n sx hints acc
          end
      | KAlign _ _ => know_lookup segs rest rb rk n sx hints acc
      | KRange _ _ _ => know_lookup segs rest rb rk n sx hints acc
      | KWr _ _ => know_lookup segs rest rb rk n sx hints acc
      | KDisj _ _ _ _ => know_lookup segs rest rb rk n sx hints acc
      end
  end.

(* [comment removed for export] *)
Definition mkAnd : ltac2:(zQ "30!lp2!hjb!lpa>2kn@1$1$2>1a$0>1b$0$0") := ltac2:(zQ "i02!lp2!j6!ja!mn8!mo3!hjb!h8!ir4!m7!moc!iqe!jta!isc!io4!it1!hu5!hvb!mle!mp5!jgc!jj7!iq8!mpf!lkd!q1!it6!mq6!lpa!mr4!mrb!msa!mt4&\2op$f\2a0$0\2b0$0@3$4$3^5^4&\2op$h0\2a0$0\2b0$0@3$4$3^5^4\2kn@1$5$hb\1a$0\1b$0M0\1b$0$0^1\1k$1=2k'$1@2$h8^1$9=1j$1@1$h6@2$a$9^1M2\0$2$0@2$b@2$h4@2$a$9^2@2$8+2^1@2$h7^1+k0M2\0$2$0@2$h5^1@2$h2^6^5^5=1l$hc@1$he^5M2\0$2$0@2$ha@2$8+2^2@3$e$1@1$5@2$7$1$0^1@1$hf@4$h9$1@1$5@2$7$1$0@2$a@3$c$1@1$5@2$7$1$0^1@2$h8@3$c$1@1$5@2$7$1$0^1@2$8+2^2@3$e$1@1$5@2$7$1$0^1@3$4$3^6^5=2j2$1@1$h6@2$h3^2+1M2\0$2$0@2$b@2$h4@2$h3^3+1@2$8+2^1@2$h7^1+k0M2\0$2$0@2$h5^1@2$h2^7^6@1$h1ZMd\1x@1$d$1$0@2$hd^6^1\1v$1@1$h1^1@3$4$3^6^5@3$4$3^6^5\1n$6@3$4$3^3^2~0~0~1~1\2sx$2\2lo$6\1n$6\1e$0@3$4$3^6^5\2sx$2\1k$6\1i$1\1n$6@3$4$3^6^5").

(* [comment removed for export] *)
Definition or_disjoint : ltac2:(zQ "40!lp2!ja!hjb!lpa>2kn@1$2$3>1a$0>1b$0$1") := ltac2:(zQ "e0!j6!ir4!ja!io4!lp2!jta!hue!hjb!mp5!mg3!lpa!iq8!lkd!m7\2kn@1$7$a\1a$4\1b$4M3\1x@1$3@2$1$0$0$2@2$9^3^1\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0@2$5@2$bZ^2@2$c^1@2$d+2@2$8^6^5$6").

Definition mkOr : ltac2:(zQ "30!lp2!hjb!lpa>2kn@1$1$2>1a$0>1b$0$0") := ltac2:(zQ "e0!ja!lp2!io4!j6!jk6!mtd!mo3!muc!mv6!mve!hjb!mle!lpa!ng8\2kn@1$a$c\1a$1\1b$1M2\1x@1$2$3$1@1$9^2\1x$3M2\1x@1$2$3$1@1$9^2\1y$3@1$b@3$d$7^2^1M0\0$0$1@3$5^4^3^2@3$6$4^3^2M0\0$0$1@3$5^4^2^3@3$6$4^3^2@3$8$7^3^2M0\0$0$1@3$5^3^2^1@3$6$4^2^1M0\0$0$1@3$5^3^1^2@3$6$4^2^1@3$8$7^2^1").

(* [comment removed for export] *)
Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

(* [comment removed for export] *)
Definition lin_nowrap : ltac2:(zQ "40!ja!hjb!lp2!lpa>2kn@1$1$3>1e$2$0") := ltac2:(zQ "h20!j6!ir4!hjb!lp2!ja!io4!jta!hue!isc!it1!mg3!lpa!mr4!msa!nh0!moc!iq8!lkd\2kn@1$2$b\1e$3=1l$c@1$d^1M5\1x@1$5@2$1$0$0$4@3$e@1$a^3@3$8$0@1$2@2$1$0$3^1@3$9$0@1$2@2$1$0$3^1\1p@2$1$0$0M1\1p@2$1$0$0$4^1\2lo$0\2hi$0@2$6@2$h0Z^2@2$h1^1$f$7").

Definition mkSrl : ltac2:(zQ "40!lp2!hjb!j6!lpa>2kn@1$1$3>1a$0>1s$2$0") := ltac2:(zQ "h80!j6!lp2!hjb!ir4!jta!ja!isc!it1!nhd!it6!ni3!mle!nie!njc!mq6!lpa!mr4!msa!nka!mo3!mt4!iq8!lkd!m7\2kn@1$2$f\1a$1\1s$0=1l$h0@1$h1^2=1m$0@2$h7+2^2M5\0$5$1@2$4@2$4@2$4@2$4@1$8@1$h2^2@2$e^1@3$7$0@1$2@2$3$0$1^2@2$h5Z@3$6$0@1$2@2$3$0$1^2@2$h6@3$6$0@1$2@2$3$0$1^2^1@2$d^5^4@1$h4@4$9$0@1$2@2$3$0$1Z@2$c^1@3$7$0@1$2@2$3$0$1^2@3$h3$a^4@1$b^3").

Definition mkAluK : ltac2:(zQ "40!lp2!hjb!hu5!lpa>2kn@1$1$3>2op$2>1a$0>1b$0$0") := ltac2:(zQ "f4!lp2!nl9!h8!mo3!j6!hu5!ja!io4!hvb!hjb!nm2!nma!mve!lpa!nn3&\3op0$5\2a0$0\2b0$0@3$1^8^5^6&\3op0$8\2a0$0\2b0$0@3$1^8^5^6&\3op0$5\2a0$0\2b0$0@3$1^7^5^4&\3op0$8\2a0$0\2b0$0@3$1^7^5^4\2kn@1$9$d\2op$5\1a$0\1b$0M5\2op$5$0^3@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1M7\1x@1$7$4$0@1$c^2\1z$4@3$3^4^3^2M7\1x@1$7$4$0@2$e^1+6\1s$4@3$b^5^3^1@3$3^3^2^1@3$3^3^2^1@3$a^4^2^1M0\1a$0$0^2\1z$4M0\1b$0$0^2\2z0$4@3$1^6^4^3\1n$2@3$1^6^3^4~0~0~1~1\2sx$6\2lo$2\1n$2\1e$0@3$1^9^6^7\2sx$6\1k$2\1i$4\1n$2@3$1^9^6^7\1n$2@3$1^5^3^2~2~2~3~3\2sx$6\2lo$2\1n$2\1e$0@3$1^8^6^5\2sx$6\1k$2\1i$4\1n$2@3$1^8^6^5").

Definition msize_bytes : ltac2:(zQ "20!h8!nnf>2sz$1$0") := ltac2:(zQ "20!nnf!h8\2sz$0M0\2sz$0$1^1N1N2N4N8").

(* [comment removed for export] *)
Definition flat_sc : ltac2:(zQ "50!hjb!h8!lpa!mh9!no8>2kn@1$0$2>1a$3>1n$1@1$0$4") := ltac2:(zQ "h50!j6!no8!hjb!ir4!np4!jgc!ja!np9!io4!npf!mi2!nq9!iq8!jta!h8!mk1!mib!lpa!mh9!le!m7\2kn@1$2$h1\1a$h2\1n$eM8\1x@1$8@2$3$0$0@1$2$1@2$f^3@1$h0^2\1p@2$3$0$0M3\1p@2$3$0$0@1$2$1^1\2lo$0\2hi$0M6\0$6@1$2$1@2$d@2$cZ@2$5^2@1$a^5@2$c@2$5@2$5^1@1$a^5@1$h3^4@2$h4+2+k0@1$4$1@3$7$1@2$9^5@1$b^4@1$4$1@3$7$1@2$9^2@1$b^1@1$4$1").

(* [comment removed for export] *)
Fixpoint wr_covered (kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (expr_eqb (a_base a) kb && Z.leb kk (a_off a) && Z.leb (a_off a + Z.of_nat n) (kk + len))%bool
      then true else wr_covered rest a n
  | _ :: rest => wr_covered rest a n
  end.

Definition storeok_sc : ltac2:(zQ "50!hjb!h8!lpa!mh9!no8>2kn@1$0$2>1a$3>1n$1@1$0$4") := ltac2:(zQ "a0!no8!ja!hjb!np4!np9!h8!nr1!nrf!lpa!mh9\2kn@1$2$8\1a$9\1n$5M1\0$1@1$2$0@3$6^3^2^1@1$3$0@3$4$0@2$7^2^1@1$3$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Record scripts : Type := SCR {
  sc_dirs  : list bool;     (* [comment removed for export] *)
  sc_reads : list expr;     (* [comment removed for export] *)
  sc_hints : list bool      (* [comment removed for export] *)
}.

Inductive stepres :=
| SOk (ss : sym_state) (scs : list sidecond) (scr : scripts)
| SStop.

Definition lit_branch : ltac2:(zQ "30!j6!ja!nsc>1c$2>1x$0>1y$0$1") := ltac2:(zQ "50!md!j6!hi3!nsc!ntb\1c$3\1x$1\1y$1@3$4^3@2$2@1$0#k0^2@2$2@1$0#k0^1").

(* [comment removed for export] *)
Definition cond_on_eq : ltac2:(zQ "20!ja!nsc>1c$1$0") := ltac2:(zQ "40!hue!hv5!nsc!ja\1c$2M2\1c$2$3^1$1$0$0$1$0$1").

(* [comment removed for export] *)
Definition itv_ltu : ltac2:(zQ "30!j6!ja!io4>2al$0>2ah$0>2bl$0>2bh$0@1$2$1") := ltac2:(zQ "90!ja!j6!ip9!io4!ip3!hue!hv5!iq8!lkd\2al$1\2ah$1\2bl$1\2bh$1M0\0$0@1$3$0@2$8^3^2@2$2$0$6M0\0$0@1$3$0@2$7^1^4@2$2$0$5@1$4$0").

(* [comment removed for export] *)
Definition itv_lts : ltac2:(zQ "30!j6!ja!io4>2al$0>2ah$0>2bl$0>2bh$0@1$2$1") := ltac2:(zQ "d0!ja!j6!jta!iq8!lkd!io4!ip9!ip3!hue!kve!hv5!nub!m7\2al$1\2ah$1\2bl$1\2bh$1=1h$1@2$c+2+jfM0\0$0@1$5$0@2$9@2$2@2$4^4^1@2$4^2^1@2$2@2$3^1^5@2$3^1^3@4$b^5^4^3^2M0\0$0@1$5$0@2$2@2$3^1^5@2$4^2^1@2$6$0$aM0\0$0@1$5$0@2$2@2$4^4^1@2$3^1^3@2$6$0$8@1$7$0").

Definition range_branch : ltac2:(zQ "40!j6!ja!io4!nsc>1c$3>2al$0>2ah$0>2bl$0>2bh$0@1$2$1") := ltac2:(zQ "h01!ja!jj7!io4!ip9!jta!j6!lkd!nsc!ip3!hue!nhd!nv6!kve!hv5!og2!nub&@2$4@2$4@2$1^4^3@2$1^2^1@2$1^4^2\1c$7\2al$5\2ah$5\2bl$5\2bh$5M7\1c$7@1$2$0^5M0\0$0@1$2$0@2$c@2$6^3^2@2$6^1^4@2$3$0$9M0\0$0@1$2$0~0@2$3$0$d@1$8$0M0\0$0@1$2$0@2$c@2$6^3^2@2$6^1^4@2$3$0$dM0\0$0@1$2$0~0@2$3$0$9@1$8$0@4$e^4^3^2^1@4$b$0$0$a@4$e^4^3^2^1@4$f^4^3^2^1@4$b$0$0$a@4$f^4^3^2^1").

(* [comment removed for export] *)
Definition decide_branch : ltac2:(zQ "60!lp2!ja!hjb!io4!nsc!lpa>2kn@1$2$5>1c$4>1a$0>1b$0@1$3$1") := ltac2:(zQ "h2i6!j6!ja!io4!ir4!ip3!mg3!lp2!ip9!ogd!ohb!mj5!h8!hu5!hvb!hjb!nsc!oib!lpa&\2bl$0\2bh$0@5$9^d^5^4^2^1&M3\2p0@2$3$0$0@1$2$1^1~0&\2p0@2$3$0$0~1&M2\1x@1$2@2$3$0$0@1$2$1@2$5^b^8~2@1$4$1&\2ah$0~3&\2al$0~4&M3\1p@2$3$0$0@1$2$1^1~5&\1p@2$3$0$0~6&M2\1x@1$2@2$3$0$0@1$2$1@2$5^8^6~7@1$4$1&M1\0$1@1$2$1@2$a^6^5@2$7$1@1$8^7~8&\2b0$6~9&\2a0$6~a&\2op$c~b&\2op$d~b&\2bl$0\2bh$0@5$9^e^5^4^2^1&M3\2p0@2$3$0$0@1$2$1^1~e&\2p0@2$3$0$0~f&M2\1x@1$2@2$3$0$0@1$2$1@2$5^c^9~h0@1$4$1&\2ah$0~h1&\2al$0~h2&M3\1p@2$3$0$0@1$2$1^1~h3&\1p@2$3$0$0~h4&M2\1x@1$2@2$3$0$0@1$2$1@2$5^9^7~h5@1$4$1&M1\0$1@1$2$1@2$a^7^6@2$7$1@1$8^8~h6&\2bl$0\2bh$0@5$9^c^5^4^2^1&M3\2p0@2$3$0$0@1$2$1^1~h8&\2p0@2$3$0$0~h9&M2\1x@1$2@2$3$0$0@1$2$1@2$5^a^7~ha@1$4$1&\2ah$0~hb&\2al$0~hc&M3\1p@2$3$0$0@1$2$1^1~hd&\1p@2$3$0$0~he&M2\1x@1$2@2$3$0$0@1$2$1@2$5^7^5~hf@1$4$1&M1\0$1@1$2$1@2$a^5^4@2$7$1@1$8^6~i0&\2b0$6~i1&\2a0$6~i2&\2op$c~i3&\2op$d~i3\2kn@1$e$h1\1c$f\1a$6\1b$6M6\1a$6@1$2$1^2\1x$0M6\1b$6@1$2$1^2\1y$0@2$7$1@3$h0^5^2^1\1n$bM1\0$1@1$2$1@2$a^4^3@2$7$1@1$8^5M2\1x@1$2@2$3$0$0@1$2$1@2$5^6^4\1p@2$3$0$0M3\1p@2$3$0$0@1$2$1^1\2al$0\2ah$0M2\1x@1$2@2$3$0$0@1$2$1@2$5^9^6\2p0@2$3$0$0M3\2p0@2$3$0$0@1$2$1^1\2bl$0\2bh$0@5$9^b^5^4^2^1@1$4$1@1$4$1~c~c~d~d\2sx$1\2lo$b\1n$b\1e$6~h7\2sx$1\1k$b\1i$0\1n$b~h7\1n$bM1\0$1@1$2$1@2$a^3^2@2$7$1@1$8^4M2\1x@1$2@2$3$0$0@1$2$1@2$5^5^3\1p@2$3$0$0M3\1p@2$3$0$0@1$2$1^1\2al$0\2ah$0M2\1x@1$2@2$3$0$0@1$2$1@2$5^8^5\2p0@2$3$0$0M3\2p0@2$3$0$0@1$2$1^1\2bl$0\2bh$0@5$9^a^5^4^2^1@1$4$1@1$4$1~i4~i4~i5~i5\2sx$1\2lo$b\1n$b\1e$6~9\2sx$1\1k$b\1i$0\1n$b~9").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Fixpoint closedb (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => closedb a && closedb b
  | EExt _ _ _ a => closedb a
  | EBlob _ _ _ _ => false
  end.

Fixpoint esubst (s r e : expr) : expr :=
  if expr_eqb e s then r else
  match e with
  | EAlu op a b => EAlu op (esubst s r a) (esubst s r b)
  | EAluw op a b => EAluw op (esubst s r a) (esubst s r b)
  | EMd op a b => EMd op (esubst s r a) (esubst s r b)
  | EMdw op a b => EMdw op (esubst s r a) (esubst s r b)
  | EExt sx lo n a => EExt sx lo n (esubst s r a)
  | _ => e
  end.

(* [comment removed for export] *)
Fixpoint eval_closed (e : expr) : option Z :=
  match e with
  | ELit z => Some (z mod two64)%Z
  | EVar _ => None
  | EAlu op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zalu op x y) | _, _ => None end
  | EAluw op a b => match eval_closed a, eval_closed b with
                    | Some x, Some y => Some (zaluw op x y) | _, _ => None end
  | EMd op a b => match eval_closed a, eval_closed b with
                  | Some x, Some y => Some (zmd op x y) | _, _ => None end
  | EMdw op a b => match eval_closed a, eval_closed b with
                   | Some x, Some y => Some (zmdw op x y) | _, _ => None end
  | EExt sx lo n a => match eval_closed a with
                      | Some x => Some (zext_lit sx lo n x) | None => None end
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint subexprs (e : expr) : list expr :=
  match e with
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => subexprs a ++ subexprs b ++ [e]
  | EExt _ _ _ a => subexprs a ++ [e]
  | _ => [e]
  end.

(* [comment removed for export] *)
Fixpoint all_eval_to (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match eval_closed (esubst s (ELit lo) e) with
           | Some w => Z.eqb w v && all_eval_to s e v (lo + 1) c
           | None => false
           end
  end.

Definition conc_limit : Z := 4096.

Fixpoint conc_try (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match eval_closed (esubst s (ELit lo) e) with
            | Some v => if all_eval_to s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                        else conc_try kn e rest
            | None => conc_try kn e rest
            end
          else conc_try kn e rest
      | None => conc_try kn e rest
      end
  end.

Definition concretize : ltac2:(zQ "50!hjb!io4!j6!lp2!lpa>2kn@1$0$4>1e$3@1$1$2") := ltac2:(zQ "a0!ja!hjb!io4!j6!oj9!ok4!ol0!olf!lp2!lpa\2kn@1$1$9\1e$8M0\0$0@1$2$3@1$4^1@1$6^1@3$5^2^1@1$7^1").

(* [comment removed for export] *)
Definition conc_expr : ltac2:(zQ "30!lp2!hjb!lpa>2kn@1$1$2>1e$0$0") := ltac2:(zQ "b6!lp2!j6!io4!mle!omb!h8!ja!hu5!hvb!hjb!lpa&M2\1x@1$2$1$0@2$4^5^4\1v$1@1$3^1^4&\1b$0~0&\1a$0~1&\2op$7~2&\2op$8~2&M2\1x@1$2$1$0@2$4^6^5\1v$1@1$3^1^5\2kn@1$9$a\1e$0M0\1e$0$0^1\1z$1^2\1n$5M2\1x@1$2$1$0@2$4^3^2\1v$1@1$3^1^2~3~3~4~4\2sx$6\2lo$5\1n$5\2e0$0~5\2sx$6\1k$5\1i$1\1n$5~5").

(* [comment removed for export] *)
Definition to_saddrK : ltac2:(zQ "50!hjb!j6!lp2!lpa!mh9>2kn@1$0$3>1e$2>3imm$1$4") := ltac2:(zQ "h26!j6!io4!mle!lp2!mh9!on9!jk6!omb!oo5!mo3!h8!ja!ir4!hu5!hvb!hjb!lpa!oob&M1\1x@1$1$0$4@2$7^8@3$9$6^7@1$2^6\1v$0@2$8@1$2Z^1@2$5^7^6&\1b$3~0&\1a$3~1&\2op$d~2&\2op$e~2&M1\1x@1$1$0$4@2$7^9@3$9$6^8@1$2^7\1v$0@2$8@1$2Z^1@2$5^8^7\2kn@1$f$h0\1e$3\3imm$0Mc\1x@2$c$3$0$4@1$h1^2\2e0$3\1z$0M3\2e0$3$4^2\2z0$0@2$5^5^4\1n$aM1\1x@1$1$0$4@2$7^6@3$9$6^5@1$2^4\1v$0@2$8@1$2Z^1@2$5^5^4~3~3~4~4\2sx$b\2lo$a\1n$a\2e1$3~5\2sx$b\1k$a\1i$0\1n$a~5").

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK (s_know ss) op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK (s_know ss) op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK (s_know ss) op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluw ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMd op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr (s_know ss) (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branch (s_know ss) c a b with
            | Some t => Some t
            | None => decide_branch (s_know ss) c (conc_expr (s_know ss) a) (conc_expr (s_know ss) b)
            end with
      | Some t => SOk (sjump ss (if t then tk else p + 4)) [] scr
      | None =>
          match sc_dirs scr with
          | [] => SStop
          | t :: dirs' =>
              SOk (sjump ss (if t then tk else p + 4)) [SCBr t c a b]
                  (SCR dirs' (sc_reads scr) (sc_hints scr))
          end
      end
  | Fence _ _ _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | FenceI _ _ _ => SOk (sjump ss (p + 4)) [] scr
  | Load sz sx rd rs imm =>
      let n := msize_bytes sz in
      (* [comment removed for export] *)
      let sx' := match sz with SZ8 => false | _ => sx end in
      let a := to_saddrK (s_know ss) (g rs) (bv_signed imm) in
      let fin v scs hints :=
        SOk (sset ss rd v (p + 4)) (flat_sc (s_know ss) a n ++ scs)
            (SCR (sc_dirs scr) (sc_reads scr) hints) in
      match log_lookup (s_know ss) (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
      | LStuck => SStop
      | LHit v scs hints => fin v scs hints
      | LMiss scs hints =>
          match know_lookup segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
          | LStuck => SStop
          | LHit v scs' hints' => fin v scs' hints'
          | LMiss scs' hints' =>
              (* [comment removed for export] *)
              let i := s_next ss in
              let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
              let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
              SOk (SS (p + 4)
                      (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) rv)
                      (s_log ss) (s_know ss) (S i))
                  (flat_sc (s_know ss) a n ++ SCReadBase a n sx' rv :: scs')
                  (SCR (sc_dirs scr) reads' hints')
          end
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK (s_know ss) (g rs1) (bv_signed imm) in
      SOk (SS (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss))
          (flat_sc (s_know ss) a n ++ storeok_sc (s_know ss) a n) scr
  | _ => SStop
  end.

(* [comment removed for export] *)
Definition sidecond_eqb : ltac2:(zQ "20!no8!ja>1x$0>1y$0$1") := ltac2:(zQ "ba!lp2!mh9!hue!ja!no8!h8!jta!op8!nsc!mj5!kh4&\5taken$3\1c$8\2a0$0\1b$0$2&\2a1$1\2n1$0\2a2$1\2n2$0$2&\2a0$1\2n0$5\2sx$3\1e$0$2&\5taken$3\1c$8\2a0$0\2b0$0$2&@2$6@2$6@2$7^8^4@2$9^7^3@2$7^6^2&@2$6~4@2$9^5^1&\2m'$0~5&\2b'$1~6&\2n'$0~7&\2a'$1~8\1x$4\1y$4M4\1x$4$3^2\5taken$3\1c$8\1a$0\1b$0$2\1a$1\1n$0M4\1y$4$3^3~0\2a'$1\2n'$0@2$6@2$7^4^2@2$9^3^1~1~1\2a0$1\2n0$5$2~2\2a0$0\1b$0$2\1a$1\1n$0\1b$1\1m$0M4\1y$4$3^5~3\2a0$1\2n0$0$2~9~1\2a0$1\2n0$5$2~2\2a0$0\2b0$0$2\1a$1\1n$0\1b$1\1m$0M4\1y$4$3^5~3\2a0$1\2n0$0$2~1~9\2a0$1\2n0$5$2~2\2a0$0\2b0$0$2\1a$1\1n$5M4\1y$4$3^3~0\2a0$1\2n0$0$2~1~1\2a'$1\2n'$5@2$6@2$7^4^2@2$a^3^1~2\2a0$0\1b$0$2\1a$1\1n$5\2sx$3\1e$0$2\1a$0\1b$0$2").

Fixpoint sc_mem (x : sidecond) (l : list sidecond) : bool :=
  match l with [] => false | y :: t => sidecond_eqb x y || sc_mem x t end.

Fixpoint sc_add (news acc : list sidecond) : list sidecond :=
  match news with
  | [] => acc
  | x :: t => sc_add t (if sc_mem x acc then acc else x :: acc)
  end.
End FPX2.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Variable segs : ltac2:(zQ "20!hjb!ph5@1$0$1").

(* [comment removed for export] *)
Fixpoint sym_exec (fuel : nat) (first : bool) (stops : list Z) (scr : scripts)
                  (ss : sym_state) (acc : list sidecond)
  : sym_state * list sidecond * scripts :=
  match fuel with
  | O => (ss, acc, scr)
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (ss, acc, scr) else
      match fetch_word segs (Z_to_bv 64 (s_pc ss)) with
      | None => (ss, acc, scr)
      | Some w =>
          if is_ecall w then (ss, acc, scr) else
          match decode_any w with
          | None => (ss, acc, scr)
          | Some (i, sz) =>
              if negb (Z.eqb sz 4) then (ss, acc, scr) else
              match sym_step segs i ss scr with
              | SOk ss' scs scr' => sym_exec f false stops scr' ss' (sc_add scs acc)
              | SStop => (ss, acc, scr)
              end
          end
      end
  end.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Definition prune1 : ltac2:(zQ "70!hjb!lpa!ja!ir4!h8!mh9!no8>5allkn@1$0$1>2wa$5>1w$4>1K$1>5hints@1$0$2@2$3@2$3@1$0$1@1$0$6@1$0$2") := ltac2:(zQ "i5id!hjb!lpa!no8!ja!ir4!np4!it6!lp2!np9!j6!h8!jgc!mle!le!iqe!iq8!mh9!oo5!lkd!m7!hu5!hvb!hue!mib!mj5!ljd!q1!oq5!kve!oqa!or5!ord!mi2!nq9!lj7!os6!ot0&@2$4@2$4@1$0$1@1$0$2@1$0$3&@4$6@1$0$1@1$0$2@3$8$1^6@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~1^5&@4$6@1$0$1@1$0$2@1$5$1@1$5$2&\1a$h0~0&\0$3~0&@4$6@1$0$1@1$0$2@3$8$1^9@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~6^8&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^8&\3len$7~0&@4$6@1$0$1@1$0$2@3$hb$1^3^1@1$5$2&@4$6@1$0$1@1$0$2@3$8$1^b@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~b^a&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^a&M3~5@2$f@2$b^9@1$d^c^4~c~d&\1b$7~e&\1a$7~f&\2op$h4~h0&\2op$h5~h0&@4$6@1$0$1@1$0$2@3$8$1^c@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~h3^b&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^b&M3~5@2$f@2$b^a@1$d^d^5~h4~h5&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^9&M3~5@2$f@2$b^a@1$d^d^4~h4~h5&\1b$7~h8&\1a$7~h9&\2op$h4~ha&\2op$h5~ha&@4$6@1$0$1@1$0$2@3$8$1^d@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~hd^c&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^c&M3~5@2$f@2$b^b@1$d^e^5~he~hf&@2^5@2$h1@1$cZ^4@1$c@2$e^3^4&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^7&M3~5@2$h2@2$e^3^4@2$h3+2+k0~i1~i2&\1p$hd~i3&@2^6@2$h1@1$cZ^5@1$c@2$e^4^5&M3~5@2$h2@2$e^4^5@2$h3+2+k0~i5~8&\1b$7~i6&\1a$7~i7&\2op$h4~i8&\2op$h5~i8&@2^7@2$h1@1$cZ^6@1$c@2$e^5^6&M3~5@2$h2@2$e^5^6@2$h3+2+k0~ib~h7\5allkn@1$0$1\2wa$h0\1w$a\1K$1\5hints@1$0$3=1k$9@1$i0^4=8diffbase>2ka$h0>2kl$7~0\2ka$h0\2kl$7=5apart$3M7\2kl$7$3^1\1l$9@7$i4^9@1$h7^8^4@1$d^7@1$h7^3@1$i0^3@2$ha^1@2$h3+2+k0\1n$a$h6\2op$h4\1a$7\1b$7$h6\2op$h4\1a$7\1b$7$h6\2op$h5\1a$7\1b$7$h6\2op$h5\1a$7\1b$7$h6\2sx$3\2lo$a\1n$a\1e$7$h6\2sx$3\2k0$a\1i$9\1n$a$h6M3\5apart$3~0^1~2M0\5hints@1$0$3~0^5@4$6@2$4@1$0$1@1$0$2@1$0$3~3@1$5$3\1b$3\2hs@1$0$3M3\1b$3~0^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$8$1^8@1$5$1@3$8$2@4$i3^a@1$i1^9^5^4@1$5$2^1@4$6@2$4@1$0$1@1$0$2@1$0$3~3^1M1\1K$1~0^4\1a$h0\2w'$a\1v$7Mh0~4^3\2kb$7\2kk$9M3~5@2$h8^2@1$h7^bM3~5@2$hc@2$f@2$b^1@1$d^4^7@2$f@2$b^7@1$d^a^1~7~8@2^6@2$h1^2^1@1$i1^4\1a$h0\3len$7Mh0~4^2\2kb$7\2kk$9M3~5@2$h8^2@1$h7^aM7~9^3\2l0$9=1l$9@2$ha^1@2$h3+2+k0=3hi1$9@2$h9^8@2$b^3^1=2r1@1$0$1M3\0$3@1$0$1@2$h2^4^1@3$8$1@2$hf@2$h1^5^4@1$c@2$e^1^4@1$5$1@1$5$1=3lo2$9@2$i2^5@2$b^a@1$d^d=2r2@1$0$1M3\0$3@1$0$1@2$h2^1@2$b^6^4@3$8$1@2$hf@2$h1^7^1@1$c@2$e@2$b^6^4^1@1$5$1@1$5$1@4$6@2$4@1$0$1@1$0$2@1$0$3~a^d\1n$aM3~5@2$f@2$b^7@1$d^a^2~7~8~h1~h1~h2~h2\2sx$3\2lo$a\1n$a\1e$7~h6\2sx$3\2k0$a\1i$9\1n$a~h6@2^5@2$h1^2^1^3\1a$h0\3len$7\2bk$aMh0~4^3\2kb$7\2kk$9M3~5@2$h8^2@1$h7^bM7~9^4\2l0$9=1l$9@2$ha^1@2$h3+2+k0M3~5@2$hc@2$f@2$b^3^1^9@2$f@2$b^9@1$d^c^3~c~d\1n$aM3~5@2$f@2$b^8@1$d^b^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$8$1^a@1$5$1@1$5$2^9~h7~hb~hb~hc~hc\2sx$3\2lo$a\1n$a\1e$7~i0\2sx$3\2k0$a\1i$9\1n$a~i0@2^6@2$h1^2^1^4\2lo$9\2hi$9M7\1x$7~0@1$h7^8\1z$9M9\1z$9~0^1=2r1@1$0$1M3\0$3@1$0$1@2$h2^3@2$h9^5^2@3$8$1@2$he^3@2$h9^5^2@1$5$1@1$5$1=3lo2$9@2$i2^4@2$b^6@1$d^9=2r2@1$0$1M3\0$3@1$0$1@2$h2^1^4@3$8$1@2$he^1^4@1$5$1@1$5$1@4$6@2$4@1$0$1@1$0$2@1$0$3~a^9~i4~i4\1n$aM3~5@2$h2@2$e^2^3@2$h3+2+k0@2^4@2$h1@1$cZ^3@1$c@2$e^2^3@4$6@2$4@1$0$1@1$0$2@1$0$3~3^6~i9~i9~ia~ia\2sx$3\3lo0$a\1n$a\1e$7~ic\2sx$3\2k0$a\1i$9\1n$a~ic\1e$7\1m$9~2\1e$7\2lo$9\2hi$9@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$8$1^7@1$5$1@1$5$2^6\1a$h0\1n$9~2\2a1$h0\2n1$9\2a2$h0\2n2$9@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$8$1^8@1$5$1@1$5$2^7").

Fixpoint prune (allkn : list kentry) (wa : saddr) (w : nat) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1 allkn wa w K hints in
      let '(r, scs2, hs2) := prune allkn wa w rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Fixpoint carry (log : list sentry) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match log with
  | [] => (kn, [], hints)
  | SE a w v :: older =>
      let '(kn1, scs1, hs1) := carry older kn hints in
      let '(kn2, scs2, hs2) := prune kn1 a w kn1 hs1 in
      (KWord a w v :: kn2, scs1 ++ scs2, hs2)
  end.
End FPX3.


End SX2.
(* [comment removed for export] *)
