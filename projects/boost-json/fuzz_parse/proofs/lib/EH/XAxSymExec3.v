(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes03nat37Corelib7Numbers7BinNumshd1Z04bool46Stdlib6ZArith6BinInt1Zk03mulk06of_natk03powhd4Npos46Stdlib6NArith6BinNat1Nn43muln46of_natk03divk06modulo35stdpp9bitvectorbdefinitionsqa8bv_swrapqa2bv99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX25FPX_1~~~~~~t75ext_Zqa7Z_to_bvqabbv_unsigned04list37Corelib5Lists7ListDefhk86firstnhk85skipnk06to_nat3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasehnbdbytes_le_to_Zt7ablob_bytes3h5LinuxProcessSemantics5Riscv5Instrhs85aluop05false04truehs85mulop3h5LinuxProcessSemantics5Riscv3Semigb5alu64igb5low323h5LinuxProcessSemantics5Riscv7Preludeijf4sextigb5alu32igb7mul_divt77ext_val06optiont74expr04None04Somet75two64k03subk03oppk04onest76two64zk03lebt76two63zt77mtwo63zt77ones64zk04landk03ltb37Corelib4Init5Logiciva2eqt75snormt79snorm_reft76zmod64k06shiftrt76zdiv6404andbk03addt77ones32zt76two32zt74zalut76land64k03lork04lxork06shiftlt75zaluwt76land32t74sx32t73zmdt76wrap64t75zfastt76zfastwt76zfastm04prod0acomparisont73lin03fst03snd04pairt74lins36Stdlib5Lists4Listjv8afold_rightt7clscale_termshs85M_MULt74ELitt73EMdk03eqbt76ltermshs87ALU_ADDt74EAlut7acoeffs_divt76lin_oft7blin_lowbits46Stdlib5Arith8PeanoNat3Natko33eqbt74EExtt78lmerge_ft76is_litt78shamt_oft75unlint74laddt76lscalet76lmerget76zalu_lt75EAluwt77zaluw_lt75zmd_lt74EMdwt74zmdw37Corelib4Init3Natlhd3addko33lebt79zext_fastiva1Ihk83nthijf6bv_eqbt74ridxqa2BVqa4BvWft75saddrt72SAt79split_litt73envt76a_baset75a_offt76edenot79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~lqb6v_addit78expr_eqb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~lvf9sym_statelvf4exprlvf6s_regslvf3SSRlvf4ridxlvf6s_knowlvf5s_loglvf6s_nextlvf6s_resvlvf6sr_updlvf4s_pclvf5saddr99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX25FPX_2~~~~~~mr48rangerel03orbmr49RDisjointmr47RInsidemr48RPartialmr48RUnknownlvf8expr_eqblvf4ELitlvf5two64lvf6zdiv64lvf7two64m1k03maxk03mink07log2_uplvf6two63zlvf3linlvf6kentry99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX25FPX_3~~~~~~nq3aall_factsbnq38is_factbjv86filternq38facts_oflvf8erange_flvfberange_fuelnq36erangenq38ctz_fuelnq36lins_elvf6lin_ofhs87ALU_ANDlvf4EAlunq3ffind_and_atom_knq3cpageup_low_khd8positivenq35ctz64nq3apageup_lownq37ealign0nq3cpageup_alignlvf9lin_rangek04log2nq35sfact04consnq39sum_factsnq39sum_substnq3clin_test_relnq3blin_nowrapRnq38lin_testnq36lsub_enq3alin_apart0nq3ashares_varnq3alin_brangenq3alin_srangenq36zlit6403nilnq37lin_ge0nq33xhinq33xlonq3abase_rangenq36novarsnq38xinside0nq3bxinside_numlvf5a_offlvf6a_basenq37xinsidenq3bkdisj_apartnq39lin_apartlvf5mkAlulvfafind_rangenq36end_hi04negbnq3dkdisj_apart_xnq3cranges_apartnq35sprepnq35SPrepnq3adisj_sidesnq3cdisj_sides_x99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX25FPX_4~~~~~~qod6pt_getqod6pt_setlvf5ptreeiva3notlvf6PTLeafqodezbytes_le_to_Zhk86repeatqodclit_of_bytes3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTyperj27Segmentqod4lreslvf8sidecondqod4LHitqod5LMissqod6LStuckqodeknow_bytes_litqoddknow_lookupA0qodcknow_lookupAqodbcoeffs_divklvfapageup_lowlvf6erangehs87ALU_SRLlvf5unlinqodaldiv_termslvfalin_nowraplvfblin_trivialqodclin_nowrap_lqodblsplit_divclvfacoeffs_divqodelin_lowbits_knqodalsplit_divqod5mkSrllvf6ealignlvf4mkMdqodeand_high_splitqoddand_low_splitqod7lowbitslvf5ctz64lvf3xhiqod6mkAnd0qodbnarrow_maskqod5mkAndhs86ALU_ORqod6mkAndKk04lnotqodbor_disjointlvf6is_litlvf4zaluqod5evalSlvf6wrap64qod8nubE_accqod7closedbqod8conc_tryqodbeval_closedqod4nubEqod8subexprsqodaconcretizehs8bbranch_condigbcbranch_takenqod7itv_ltu0aoption_mapqod7itv_ltshs87ALU_SUBlvf7lin_ge0qodacond_on_eqqodbdiff_branchqodalin_branchqodcrange_branchqodalit_branchqodddecide_branchqod5mkSlths87ALU_SLThs88ALU_SLTUhs85BC_LThs86BC_LTUqod4mkOrlvf8shamt_ofqod5foldKqod7mkAluK0qod6mkAluKqod8pow2_loglvf6mkAluwqod7zband32qodbsx32_stableqod5zsx32qod8mkAluwK0qod5extK0hs85msizelvf6SCFlatlvf4elenlvfabase_rangeqodawr_coveredlvf9SCStoreOklvf8to_saddrlvf2SAlvf9split_liths86awidthhs83SZ4hs83SZ8lvf9saddr_eqbhs85amoophs87ALU_XORqod7mkAluwKhs85instrqod4itab3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsvs1afetch_wordvs18is_ecall3h5LinuxProcessSemantics5Riscv7DecodeChgh2adecode_anya9OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX25FPX_48WithSegs~~~~~~hgk7aitab_entryqodbitab_lookuphgk7aitab_soundhgk7cmk_itab_fuelqod7scriptsqod3SCRlvf8rangerellvf7rel_litlvf7xinsidehgk79zf_coversk04of_Nrj28seg_baserj28seg_sizejv87forallbhgk7asegs_avoidhgk7ekentry_overlayhgk7ckwr_offimagehgk7fkentry_readablehgk7eknow_bytes_covjv87existsbhgk7bkn_readablehgk78evars_lthgk7akn_overlaylvf8facts_ofko33ltb36Stdlib4Bool4Boolhhu93eqbhgk7dfind_readbasehgk7fx_dischargeablehgk7cesize_budgeths84ffmths85csrophs87fcvt_tyhs86fariophs86fcmpophs85fmaophs89fminmaxophs86fmvdirhs86fsgnop01Slvf4EVarhgk78esize_lehgk75rd_oflvf6sr_getqod7stepresqod5SStopqod3SOkhgk76cap_rdhgk78x_filterqod8sym_steplvf3clrhgk7dsym_execTX_goqod4kcutlvf5KZerolvf5KFilllvf4KUnk03applhd3sublvf5KWordlvf5mkExt04unit02ttqod5ktrimlvferanges_apart_xqod8prune_zflvf4KImgqod9kword_cutlvf6SCDisjlvf5spreplvferanges_apart_plvf6end_hilvf6sp_rnglvfain_sides_xlvfashares_varlvf5sp_Dxlvf5sp_h1lvf6zlit64lvf8in_sideslvf9lin_apartlvf4sp_Dqod7prune1pqodfranges_apart_pcqod9kfill_cutqod8kunk_cutqod9kzero_cut" s.
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module AX2.
Section FPX_1. Context {fx : XPropExec.FPState}.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

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

Definition ext_val : ltac2:(zQ "40!h8!md!t2!ja>2sx$3>2lo$0>1n$0>1v@1$2@1$1#k0@1$2@1$1#k0") := ltac2:(zQ "70!md!h8!ja!hi2!hia!t2!hj4\2sx$2\2lo$1\1n$1\1v@1$5@1$0#k0@2$4@1$0#k0@4$3^4^3^2@2$6@1$0#k0^1").

Definition blob_bytes : ltac2:(zQ "50!hk2!md!t2!h8!j6>2bs@1$0@1$2@1$1#8>1i$4>1n$3@1$0@1$2@1$1#8") := ltac2:(zQ "80!md!t2!hk2!h8!hlf!hm9!j6!hn2\2bs@1$2@1$1@1$0#8\1i$6\1n$3@3$4@1$1@1$0#8^1@3$5@1$1@1$0#8@1$7^2^3").

Definition blob_val : ltac2:(zQ "60!md!t2!ja!hk2!h8!j6>2sx$2>2bs@1$3@1$1@1$0#8>1i$5>1n$4@1$1@1$0#k0") := ltac2:(zQ "c0!ja!md!j6!hk2!h8!hqa!hrb!oc!p2!hia!t2!s7\2sx$0\2bs@1$3@1$a@1$1#8\1i$2\1n$4@2$9@1$1#k0=1u$2@1$5@3$6^3^2^1M0\2sx$0$2^5@2$b@2$7@1$1#8@1$8^2^1^1").

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

Definition aluop_eqb : ltac2:(zQ "20!huc!ja>1a$0>1b$0$1") := ltac2:(zQ "40!hv5!huc!ja!hvc\1a$1\1b$1M1\1a$1$2^2M1\1b$1$2^1$3$0$0$0$0$0$0$0$0$0M1\1b$1$2^1$0$3$0$0$0$0$0$0$0$0M1\1b$1$2^1$0$0$3$0$0$0$0$0$0$0M1\1b$1$2^1$0$0$0$3$0$0$0$0$0$0M1\1b$1$2^1$0$0$0$0$3$0$0$0$0$0M1\1b$1$2^1$0$0$0$0$0$3$0$0$0$0M1\1b$1$2^1$0$0$0$0$0$0$3$0$0$0M1\1b$1$2^1$0$0$0$0$0$0$0$3$0$0M1\1b$1$2^1$0$0$0$0$0$0$0$0$3$0M1\1b$1$2^1$0$0$0$0$0$0$0$0$0$3").

Definition mulop_eqb : ltac2:(zQ "20!ig2!ja>1a$0>1b$0$1") := ltac2:(zQ "40!hv5!ig2!ja!hvc\1a$1\1b$1M1\1a$1$2^2M1\1b$1$2^1$3$0$0$0$0$0$0$0M1\1b$1$2^1$0$3$0$0$0$0$0$0M1\1b$1$2^1$0$0$3$0$0$0$0$0M1\1b$1$2^1$0$0$0$3$0$0$0$0M1\1b$1$2^1$0$0$0$0$3$0$0$0M1\1b$1$2^1$0$0$0$0$0$3$0$0M1\1b$1$2^1$0$0$0$0$0$0$3$0M1\1b$1$2^1$0$0$0$0$0$0$0$3").

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
Definition zalu : ltac2:(zQ "20!j6!huc>2op$1>1x$0>1y$0$0") := ltac2:(zQ "60!md!j6!hia!huc!iid!hj4\2op$3\1x$1\1y$1@2$5@1$0#k0@3$4^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition zaluw : ltac2:(zQ "20!j6!huc>2op$1>1x$0>1y$0$0") := ltac2:(zQ "90!md!j6!ij6!hia!huc!im5!imd!t2!hj4\2op$4\1x$1\1y$1@2$8@1$0#k0Kd@3$5@1$0#i0@1$0#k0@3$6^3@1$2@2$3@1$0#k0^2@1$2@2$3@1$0#k0^1@1$7@1$0#k0").
Definition zmd : ltac2:(zQ "20!j6!ig2>2op$1>1x$0>1y$0$0") := ltac2:(zQ "60!md!j6!hia!ig2!in6!hj4\2op$3\1x$1\1y$1@2$5@1$0#k0@4$4@1$0#k0^3@2$2@1$0#k0^2@2$2@1$0#k0^1").
Definition zmdw : ltac2:(zQ "20!j6!ig2>2op$1>1x$0>1y$0$0") := ltac2:(zQ "90!md!j6!ij6!hia!ig2!im5!in6!t2!hj4\2op$4\1x$1\1y$1@2$8@1$0#k0Kd@3$5@1$0#i0@1$0#k0@4$6@1$0#i0^3@1$2@2$3@1$0#k0^2@1$2@2$3@1$0#k0^1@1$7@1$0#k0").
Definition zext_lit : ltac2:(zQ "30!h8!j6!ja>2sx$2>2lo$0>1n$0>1x$1$1") := ltac2:(zQ "70!h8!md!ja!j6!io1!hia!hj4\2sx$2\2lo$0\1n$0\1x$3@2$6@1$1#k0@4$4^4^3^2@2$5@1$1#k0^1").

Definition is_lit : ltac2:(zQ "30!iob!j6!ip3>1e$2@1$0$1") := ltac2:(zQ "90!ip3!j6!ipa!h8!ja!huc!ig2!iq0!iob\1e$0M0\1e$0@1$8$1^1\1z$1@2$7$1^1\1n$3@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2sx$4\2lo$3\1n$3\2e0$0@1$2$1\2sx$4\1k$3\1i$1\1n$3@1$2$1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Definition two64z : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!m7@2$0+2+k0").
Definition two64 : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!m7@2$0+2+k0").         (* [comment removed for export] *)
Definition two64m1 : ltac2:(zQ "10!j6$0") := ltac2:(zQ "20!iq6!iqe@2$1$0+1").   (* [comment removed for export] *)
(* [comment removed for export] *)
Definition two63z : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!m7@2$0+2+jf").
Definition mtwo63z : ltac2:(zQ "10!j6$0") := ltac2:(zQ "20!ir4!m7@1$0@2$1+2+jf").
Definition two32z : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!m7@2$0+2+i0").
Definition ones64z : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!ira@1$0+k0").          (* [comment removed for export] *)
(* [comment removed for export] *)
Definition snorm_ref : ltac2:(zQ "10!j6>1k$0$0") := ltac2:(zQ "70!j6!ja!is1!isa!q1!m7!iqe\1k$0=1m$0@2$4^1$2M1\0$1$0@2$3@2$5+2+jf^1@2$6^1$2^1").
(* [comment removed for export] *)
Definition snorm : ltac2:(zQ "10!j6>1k$0$0") := ltac2:(zQ "b0!ja!j6!it0!isa!hv5!it9!iu3!is1!iud!iv4!iqe\1k$1M0\0$0$1M0\0$0$0@2$3$5^1@2$9^1$2$4^1=1m$1@2$8^1$6M0\0$0$1@2$3$2^1@2$a^1$7^1").
Lemma land_ones64z' : ltac2:(zQ "60!j6!jge!iu3!iud!q1!m7>1a$0@3$1$0@2$3^1$2@2$4^1@2$5+2+k0").
Proof. intros a. exact (Z.land_ones a 64 ltac:(lia)). Qed.
Lemma snorm_eq : ltac2:(zQ "40!j6!jge!jh4!jhc>1k$0@3$1$0@1$2^1@1$3^1").
Proof.
  intros k. cbv beta zeta delta [snorm snorm_ref mtwo63z two63z two64z]. rewrite land_ones64z'.
  pose proof (Z.mod_pos_bound k (2 ^ 64) ltac:(lia)) as B.
  destruct (Z.leb_spec (- 2 ^ 63) k) as [H1|H1]; [|reflexivity].
  destruct (Z.ltb_spec k (2 ^ 63)) as [H2|H2]; [|reflexivity].
  destruct (Z.leb_spec 0 k) as [H3|H3].
  - rewrite (Z.mod_small k (2 ^ 64)) by lia.
    destruct (Z.leb_spec (2 ^ 63) k); lia.
  - replace (k mod 2 ^ 64)%Z with (k + 2 ^ 64)%Z.
    + destruct (Z.leb_spec (2 ^ 63) (k + 2 ^ 64)); lia.
    + symmetry. rewrite <- (Z.mod_add k 1 (2 ^ 64)) by lia. apply Z.mod_small. lia.
Qed.

(* [comment removed for export] *)
Definition zmod64 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "80!ja!j6!hv5!iu3!is1!iud!isa!iv4\1z$1M0\0$0$1M0\0$0$0@2$6Z^1@2$7^1$4$2^1@2$5^1$3").
Lemma zmod64_eq : ltac2:(zQ "50!j6!jge!ji8!q1!m7>1z$0@3$1$0@1$2^1@2$3^1@2$4+2+k0").
Proof.
  intros z. cbv beta iota delta [zmod64 two64z]. rewrite land_ones64z'.
  destruct (Z.leb_spec 0 z); [|reflexivity]. destruct (Z.ltb_spec z (2 ^ 64)); [|reflexivity].
  symmetry. apply Z.mod_small. lia.
Qed.
Definition zdiv64 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "70!ja!j6!hv5!is1!isa!iv4!jj1\1z$1M0\0$0$1M0\0$0$0@2$4Z^1@2$5^1$3$2Z@2$6^1+k0").
Lemma zdiv64_eq : ltac2:(zQ "50!j6!jge!jja!pb!m7>1z$0@3$1$0@1$2^1@2$3^1@2$4+2+k0").
Proof.
  intros z. cbv beta iota delta [zdiv64 two64z].
  destruct (Z.leb_spec 0 z); [|apply Z.shiftr_div_pow2; lia].
  destruct (Z.ltb_spec z (2 ^ 64)); [|apply Z.shiftr_div_pow2; lia].
  symmetry. apply Z.div_small. lia.
Qed.

(* [comment removed for export] *)
Definition wrap64 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "70!ja!j6!iq6!jk3!isa!iv4!q1\1z$1M0\0$0$1@2$3@2$4Z^1@2$5^1$2^1@2$6^1$2").

Definition sx32 : ltac2:(zQ "10!j6>1r$0$0") := ltac2:(zQ "40!ja!j6!jk9!iv4\1r$1M0\0$0$1@2$3^1+ogggggg0^1@2$2^1+vvvvvvvvggggggg0").

(* [comment removed for export] *)
Definition ones32z : ltac2:(zQ "10!j6$0") := ltac2:(zQ "10!ira@1$0+i0").
Definition land64 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "80!ja!j6!jk3!iu3!iq6!iud!isa!iv4\1z$1M0\0$0$1@2$2@2$6Z^1@2$7^1$4^1@2$5^1$3").
Definition land32 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "80!ja!j6!jk3!jkf!jl9!iud!isa!iv4\1z$1M0\0$0$1@2$2@2$6Z^1@2$7^1$4^1@2$5^1$3").

Definition zfast : ltac2:(zQ "20!j6!huc>2op$1>1x$0>1y$0$0") := ltac2:(zQ "f0!j6!ja!huc!iq6!iud!jm2!jk9!iv4!iqe!jm9!isa!jn2!jn8!jnf!jj1\2op$2\1x$0\1y$0M2\2op$2$0^3=1t$0@2$6^2^1M1\0$1$0@2$7^1$3^1@2$8^1$3=1t$0@2$8^2^1M1\0$1$0@2$aZ^1^1@2$6^1$3@1$9@2$d^2@2$4^1+jf@3$5^3^2^1M1\0$1$0@2$7^2^1+1Z@2$c^2^1@2$e^2@2$4^1+jf@3$5^3^2^1@2$b^2^1@2$4^2^1").

Definition zfastw : ltac2:(zQ "20!j6!huc>2op$1>1x$0>1y$0$0") := ltac2:(zQ "a0!jo8!jp0!jp9!j6!huc!iud!jk9!jnf!jj1!iqe\2op$4\1x$3\1y$3M4\2op$4$3^3@1$2@1$1@2$6^2^1@1$2@1$1@2$9^2^1@1$2@1$1@2$7@1$1^2@2$5^1+hf@3$0^3^2^1@3$0^3^2^1@3$0^3^2^1@1$2@2$8@1$1^2@2$5^1+hf@3$0^3^2^1@3$0^3^2^1@3$0^3^2^1").

Definition zfastm : ltac2:(zQ "20!j6!ig2>2op$1>1x$0>1y$0$0") := ltac2:(zQ "50!jq0!j6!ig2!jm9!l8\2op$2\1x$1\1y$1M2\2op$2$1^3@1$3@2$4^2^1@3$0^3^2^1@3$0^3^2^1@3$0^3^2^1@3$0^3^2^1@3$0^3^2^1@3$0^3^2^1@3$0^3^2^1").

(* [comment removed for export] *)
Definition zext_fast : ltac2:(zQ "30!h8!j6!ja>2sx$2>2lo$0>1n$0>1x$1$1") := ltac2:(zQ "e0!j6!ja!h8!jq6!l8!le!jnf!iqe!iq6!jk9!iud!iv4!ira!jj1\2sx$1\2lo$2\1n$2\1x$0=1k$0@2$4+8@1$5^2=1u$0@2$a@2$d^2@2$4+8@1$5^4@1$c^1M1\2sx$1$0^6M2\1n$2$0^4@1$3^1\2n0$2M1\0$1$0@2$b^2@2$6+1@2$7^3+1@1$3^2@1$3@2$9@2$7^2@2$6+1^3$8@1$3^1").

(* [comment removed for export] *)
Definition zalu_l : ltac2:(zQ "20!j6!huc>2op$1>1x$0>1y$0$0") := ltac2:(zQ "40!j6!jq6!huc!jqf\2op$2\1x$0\1y$0@3$3^3@1$1^2@1$1^1").
Definition zaluw_l : ltac2:(zQ "20!j6!huc>2op$1>1x$0>1y$0$0") := ltac2:(zQ "40!j6!jq6!huc!jr7\2op$2\1x$0\1y$0@3$3^3@1$1^2@1$1^1").
Definition zmd_l : ltac2:(zQ "20!j6!ig2>2op$1>1x$0>1y$0$0") := ltac2:(zQ "40!j6!jq6!ig2!js0\2op$2\1x$0\1y$0@3$3^3@1$1^2@1$1^1").

Definition lin : ltac2:(zQ "00T") := ltac2:(zQ "40!js9!j6!hk2!ip3@2$0$1@1$2@2$0$1$3").

Definition ctor_ix : ltac2:(zQ "20!h8!ip3>1e$1$0") := ltac2:(zQ "60!ip3!h8!ja!j6!huc!ig2\1e$0M0\1e$0$1^1\1z$3N0\1n$1N1\2op$4\1a$0\1b$0N2\2op$4\1a$0\1b$0N3\2op$5\1a$0\1b$0N4\2op$5\1a$0\1b$0N5\2sx$2\2lo$1\1n$1\2e0$0N6\2sx$2\1k$1\1i$3\1n$1N7").
Definition aluop_ix : ltac2:(zQ "20!h8!huc>2op$1$0") := ltac2:(zQ "20!huc!h8\2op$0M0\2op$0$1^1N0N1N2N3N4N5N6N7N8N9").
Definition mulop_ix : ltac2:(zQ "20!h8!ig2>2op$1$0") := ltac2:(zQ "20!ig2!h8\2op$0M0\2op$0$1^1N0N1N2N3N4N5N6N7").
Definition bool_ix : ltac2:(zQ "20!ja!h8>1b$0$1") := ltac2:(zQ "20!ja!h8\1b$0M0\1b$0$1^1N1N0").
Definition lexc : ltac2:(zQ "10!jsf>1c$0>1k$0$0") := ltac2:(zQ "10!jsf\1c$0\1k$0M0\1c$0$0^2^1^2^2").

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

Definition ladd : ltac2:(zQ "10!jtb>1x$0>1y$0$0") := ltac2:(zQ "c0!j6!ip3!js9!hk2!ju1!ju6!jtb!jub!jv1!jh4!kgb!jk9\1x$6\1y$6@4$7$0@1$3@2$2$0$1@1$9@2$b@3$4$0@1$3@2$2$0$1^2@3$4$0@1$3@2$2$0$1^1@5$a@1$3@2$2$0$1@2$2$0$1\1t@2$2$0$1\3acc@1$3@2$2$0$1@3$8@3$4$0$1^2@3$5$0$1^2^1@3$5$0@1$3@2$2$0$1^1@3$5$0@1$3@2$2$0$1^2").

Fixpoint lscale_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest =>
      let k' := snorm (m * k) in
      if Z.eqb k' 0 then lscale_terms m rest else (k', a) :: lscale_terms m rest
  end.

Definition lscale : ltac2:(zQ "20!jtb!j6>1m$1>1x$0$0") := ltac2:(zQ "b0!j6!hk2!js9!ip3!ju1!jub!ju6!jtb!kh9!jh4!l8\1m$0\1x$7@4$5$0@1$1@2$2$0$3@1$9@2$a^2@3$4$0@1$1@2$2$0$3^1@2$8^2@3$6$0@1$1@2$2$0$3^1").

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

Definition lterm : ltac2:(zQ "30!ip3!js9!j6>1t@2$1$2$0$0") := ltac2:(zQ "a0!ip3!j6!ja!ju1!ju6!js9!ki8!kj1!kj8!kje\1t@2$5$1$0M2\0$2$0@2$9@3$3$1$0^1+1@3$4$1$0^1@3$8$6@1$7@3$3$1$0^1@3$4$1$0^1").

Fixpoint lterms (ts : list (Z * expr)) : expr :=
  match ts with
  | [] => ELit 0
  | [t] => lterm t
  | t :: rest => EAlu ALU_ADD (lterm t) (lterms rest)
  end.

Definition unlin : ltac2:(zQ "20!ip3!jtb>1x$1$0") := ltac2:(zQ "d1!j6!ip3!hk2!js9!ju1!ju6!ja!kj1!kk4!kkd!kl8!jtb!kje&@1$8@3$5$0@1$2@2$3$0$1^3\1x$bM2\1x@1$2@2$3$0$1$1@3$5$0@1$2@2$3$0$1^1@1$7@3$4$0@1$2@2$3$0$1^1\1p@2$3$0$1\1l@1$2@2$3$0$1M6\0$6$1@2$c@3$4$0@1$2@2$3$0$1^3Z~0@3$a$9~0@1$7@3$4$0@1$2@2$3$0$1^3").

(* [comment removed for export] *)
Fixpoint coeffs_div (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, _) :: rest => (Z.eqb (k mod m) 0 && coeffs_div m rest)%bool
  end.

Definition lin_lowbits : ltac2:(zQ "30!j6!iob!ip3>1e$2>1k$0@1$1$0") := ltac2:(zQ "f0!j6!ip3!ja!hk2!js9!m7!ipa!iq0!ju1!iob!ju6!klf!jtb!kmc!q1\1e$1\1k$0=1l$c@1$d^2M2\0$2@1$9$0@2$b@2$5+2^2@3$a$0@1$3@2$4$0$1^1@2$7$0@2$e@3$8$0@1$3@2$4$0$1^1@2$5+2^2@1$6$0").

(* [comment removed for export] *)
Definition shamt_of : ltac2:(zQ "30!j6!iob!ip3>1e$2>4bits$0@1$1$0") := ltac2:(zQ "b2!ip3!kn5!h8!j6!ja!huc!ig2!iq0!iob!q1!m7&\2op$5\1a$0\1b$0@2$1^5^4&\2op$6\1a$0\1b$0@2$1^5^4\1e$0\4bits$3M0\1e$0@1$8$3^2\1s$3@2$7$3@2$9^1@2$a+2^2\1n$2@2$1^3^2~0~0~1~1\2sx$4\2lo$2\1n$2\2e0$0@2$1^6^5\2sx$4\1k$2\1i$3\1n$2@2$1^6^5").

(* [comment removed for export] *)
Definition ext_slice : ltac2:(zQ "20!h8!ip3>2lo$0>1n$0>1v$1$1") := ltac2:(zQ "70!ja!h8!ip3!kpe!jk3!hv5!kq5\2lo$1\1n$1\1v$2M0\0$0$2@2$4@2$3^3N0@2$3^2N8^1@4$6$5^3^2^1").
Fixpoint ext_partner (c : Z) (lo n : nat) (v : expr) (ts : list (Z * expr)) : option (nat * list (Z * expr)) :=
  match ts with
  | [] => None
  | (c', a') :: rest =>
      match a' with
      | EExt false lo' n' v' =>
          if (Nat.eqb lo' (lo + n) && Nat.leb (lo + n + n') 8 && Nat.ltb 0 n' && expr_eqb v' v
              && Z.eqb (snorm c') (snorm (c * 2 ^ (8 * Z.of_nat n))))%bool
          then Some (n', rest)
          else match ext_partner c lo n v rest with Some (m, r) => Some (m, (c', a') :: r) | None => None end
      | _ => match ext_partner c lo n v rest with Some (m, r) => Some (m, (c', a') :: r) | None => None end
      end
  end.
(* [comment removed for export] *)
Fixpoint ext_merge_step (pre ts : list (Z * expr)) : option (Z * expr * list (Z * expr)) :=
  match ts with
  | [] => None
  | (c, a) :: rest =>
      match a with
      | EExt false lo n v =>
          if Nat.ltb 0 n then
            match ext_partner c lo n v rest with
            | Some (n', rest') => Some (c, ext_slice lo (n + n') v, pre ++ rest')
            | None => ext_merge_step (pre ++ [(c, a)]) rest
            end
          else ext_merge_step (pre ++ [(c, a)]) rest
      | _ => ext_merge_step (pre ++ [(c, a)]) rest
      end
  end.
(* [comment removed for export] *)
Fixpoint lmerge_f (fuel : nat) (x : lin) : lin :=
  match fuel with
  | O => x
  | S f => match ext_merge_step [] (snd x) with
           | Some (c, a, others) => lmerge_f f (ladd (lscale c (lin_of a)) (fst x, others))
           | None => x
           end
  end.
Definition lmerge : ltac2:(zQ "10!jtb>1x$0$0") := ltac2:(zQ "20!jtb!kqc\1x$0@2$1N8^1").

Definition mkAlu : ltac2:(zQ "20!ip3!huc>2op$1>1a$0>1b$0$0") := ltac2:(zQ "f4!iob!j6!kl8!ip3!kmc!kr7!ks0!ksb!huc!kj1!kt3!kta!ku3!m7!kuc&M0\1x@1$0$1$3@2$6^2+6\1s$1@3$2^5^4@1$9^1@3$2^4^3^2&M0\1x@1$0$1$3@1$5^2\1z$1@3$2^5^4^3~0&M0\1x@1$0$1$3@2$6^1+6\1s$1@3$2^4^3@1$9^1@3$2^3^2^1&M0\1x@1$0$1$3@1$5^1\1z$1@3$2^4^3^2~2\2op$8\1a$3\1b$3M0\1x@1$0$1$3@1$5^2\1x$1M0\1x@1$0$1$3@1$5^2\1y$1@1$9@3$e^5^2^1M8\2op$8$3^4@1$7@1$c@2$a@1$4^3@1$4^2@1$7@2$a@1$4^3@2$b-1@1$4^2M0\1x@1$0$1$3@2$6^2+6\1s$1@1$7@2$b@2$d+2^1@1$4^4@3$2^4^3^2@3$2^4^3^2@3$2^4^3^2@3$2^4^3^2~1~1@3$2^4^3^2@3$2^4^3^2M8\2op$8$3^3@1$7@1$c@2$a@1$4^2@1$4^1@1$7@2$a@1$4^2@2$b-1@1$4^1M0\1x@1$0$1$3@2$6^1+6\1s$1@1$7@2$b@2$d+2^1@1$4^3@3$2^3^2^1@3$2^3^2^1@3$2^3^2^1@3$2^3^2^1~3~3@3$2^3^2^1@3$2^3^2^1").

Definition mkAluw : ltac2:(zQ "20!ip3!huc>2op$1>1a$0>1b$0$0") := ltac2:(zQ "98!iob!j6!kv5!ip3!kr7!kj1!kvd!ks0!huc&M0\1x@1$0$1$3@1$4^4\1x$1@1$5@3$6^6^1^2@3$2^5^4@1$5^1&\1s$1~0&M0\1x@1$0$1$3@2$7^2+5~1@3$2^4^3^2&M0\1x@1$0$1$3@1$4^2\1z$1@3$2^5^4^3~2&M0\1x@1$0$1$3@1$4^3\1x$1@1$5@3$6^5^1^2@3$2^4^3@1$5^1&\1s$1~4&M0\1x@1$0$1$3@2$7^1+5~5@3$2^3^2^1&M0\1x@1$0$1$3@1$4^1\1z$1@3$2^4^3^2~6\2op$8\1a$3\1b$3M0\1x@1$0$1$3@1$4^2\1x$1M0\1x@1$0$1$3@1$4^2\1y$1@1$5@3$6^5^2^1M8\2op$8$3^4@3$2^4^3^2@3$2^4^3^2~3@3$2^4^3^2@3$2^4^3^2@3$2^4^3^2~3~3@3$2^4^3^2@3$2^4^3^2M8\2op$8$3^3@3$2^3^2^1@3$2^3^2^1~7@3$2^3^2^1@3$2^3^2^1@3$2^3^2^1~7~7@3$2^3^2^1@3$2^3^2^1").

Definition mkMd : ltac2:(zQ "20!ip3!ig2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "b0!kj8!ip3!iob!j6!ig2!kr7!kmc!kta!ksb!kj1!lg7\2op$4\1a$1\1b$1M2\1x@1$2$3$1@1$5^2\1x$3M2\1x@1$2$3$1@1$5^2\1y$3@1$9@3$a^5^2^1M4\2op$4$1^4@1$8@2$7^1@1$6^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2M2\1x@1$2$3$1@1$5^1\1y$3M4\2op$4$1^4@1$8@2$7^1@1$6^3@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^4^3^2@3$0^3^2^1").

Definition mkMdw : ltac2:(zQ "20!ip3!ig2>2op$1>1a$0>1b$0$0") := ltac2:(zQ "80!iob!j6!ip3!lgf!kr7!ig2!kj1!lh6\2op$5\1a$2\1b$2M0\1x@1$0$1$2@1$4^2\1x$1M0\1x@1$0$1$2@1$4^2\1y$1@1$6@3$7^5^2^1@3$3^4^3^2@3$3^3^2^1").

(* [comment removed for export] *)
Definition mkExt : ltac2:(zQ "30!h8!ip3!ja>2sx$2>2lo$0>1n$0>1e$1$1") := ltac2:(zQ "ei0!ip3!kq5!ja!h8!j6!huc!ig2!jk3!lif!kpe!lj6!kj1!jq6!ljd&\2op$5\1a$0\1b$0@4$1^8^7^6^5&\2op$6\1a$0\1b$0@4$1^8^7^6^5&\2op$5\1a$0\1b$0@4$1^a^9^8^7&\2op$6\1a$0\1b$0@4$1^a^9^8^7&@2$7@2$a@2$8^a^9^2@2$a^2N8&M2\0$2$0~4@4$1^b@2$8^3^a^9^1@4$1^b^a^9^8&M2\3sx0$2$0^4@4$1^b^a^9^8~5&\2e'$0~6&\2n'$3~7&\3lo'$3~8&\3sx0$2~9&\1k$3\1i$4\2n0$3@4$1^b^a^9^8&\3sx0$2~b&M0\1e$0$0^4\1z$4@4$1^8^7^6^5\2n0$3@4$1^8^7^6^5~2~2~3~3~a~c&M2\0$2$0@2$7@2$9^6N0@2$9^5N8^4~d&\1b$0~e&\1a$0~f&\2op$5~h0&\2op$6~h0&\2op$5\1a$0\1b$0@4$1^b^a^9^8&\2op$6\1a$0\1b$0@4$1^b^a^9^8&@2$7@2$a@2$8^b^a^2@2$a^2N8&M2\0$2$0~h5@4$1^c@2$8^3^b^a^1@4$1^c^b^a^9&M2\3sx0$2$0^4@4$1^c^b^a^9~h6&\2e'$0~h7&\2n'$3~h8&\3lo'$3~h9&\3sx0$2~ha&\1k$3\1i$4\2n0$3@4$1^c^b^a^9&\3sx0$2~hc&M0\1e$0$0^5\1z$4@4$1^9^8^7^6\2n0$3@4$1^9^8^7^6~h3~h3~h4~h4~hb~hd&M2\0$2$0@2$7@2$9^7N0@2$9^6N8^5~he\2sx$2\2lo$3\1n$3\1e$0M0\1e$0$0^1\1x$4@1$b@4$d^5^4^3@1$c^1\2n0$3M2\0$2$0@2$7@2$9^4N0@2$9^3N8^2M0\1e$0$0^2\1z$4@4$1^6^5^4^3\2n0$3@4$1^6^5^4^3~0~0~1~1\3sx0$2\3lo'$3\2n'$3\2e'$0M2\3sx0$2$0^4@4$1^9^8^7^6M2\0$2$0@2$7@2$a@2$8^8^7^2@2$a^2N8@4$1^9@2$8^3^8^7^1@4$1^9^8^7^6\3sx0$2\1k$3\1i$4\2n0$3@4$1^9^8^7^6~h1~h1~h2~h2\3sx0$2\3lo0$3\2n0$3\2e0$0~hf\3sx0$2\1k$3\1i$4\2n0$3~hf").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition ridx : ltac2:(zQ "30!h8!md!t2>1r@1$2@1$1#5$0") := ltac2:(zQ "40!md!hn2!t2!hj4\1r@1$2@1$0#5@1$1@2$3@1$0#5^1").

Definition sr_get : ltac2:(zQ "40!ip3!hk2!md!t2>2sr@1$1$0>1r@1$3@1$2#5$0") := ltac2:(zQ "c0!md!ip3!ja!kj1!hk2!lk9!lke!ll5!llf!lm6!lmb!t2\2sr@1$4$1\1r@1$b@1$0#5M2\0$2$1@3$7@1$0#5^1@3$9@1$0#5ZKv$5@2$a@1$0#5Z@1$3Z@4$6$1@1$8^1^2@1$3Z").

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

Definition split_lit : ltac2:(zQ "30!ip3!js9!j6>1e$0@2$1$0$2") := ltac2:(zQ "93!ip3!j6!jub!h8!huc!ja!ig2!js9!kj1&\3op0$4\1a$0\2b1$0@4$2$0$1^7Z&\3op0$6\1a$0\2b1$0@4$2$0$1^7Z&\2op$6\1a$0\1b$0@4$2$0$1^4Z\1e$0M0\1e$0@2$7$0$1^1\1z$1@4$2$0$1@1$8Z^1\1n$3@4$2$0$1^2Z\2op$4\1b$0\2b0$0M4\2op$4@2$7$0$1^3M0\2b0$0@2$7$0$1^1\1z$1@4$2$0$1^3^1\1n$3@4$2$0$1^5Z~0~0~1~1\2sx$5\2lo$3\1n$3\2e0$0@4$2$0$1^8Z\2sx$5\1k$3\1i$1\1n$3@4$2$0$1^8Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z\2op$4\1a$0\1b$0@4$2$0$1^4Z~2~2\2sx$5\2lo$3\1n$3\2e0$0@4$2$0$1^5Z\2sx$5\1k$3\1i$1\1n$3@4$2$0$1^5Z").

Definition to_saddr : ltac2:(zQ "30!j6!ip3!ln2>1e$1>3imm$0$2") := ltac2:(zQ "70!j6!ip3!js9!lna!ln2!lnf!jk9\1e$1\3imm$0M2\1p@2$2$1$0$4@1$5^2\1b$1\1k$0@2$3^2@2$6^1^3").

Definition adenot : ltac2:(zQ "40!md!lob!ln2!t2>1E$1>1a$2@1$3@1$0#k0") := ltac2:(zQ "60!lp1!lpa!lq2!lob!ln2!lua\1E$3\1a$4@2$5@2$2^2@1$0^1@1$1^1").

Definition saddr_eqb : ltac2:(zQ "20!ln2!ja>1a$0>1b$0$1") := ltac2:(zQ "60!lp1!lpa!ln2!jk3!lv4!kje\1a$2\1b$2@2$3@2$4@1$0^2@1$0^1@2$5@1$1^2@1$1^1").

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
| KWr (a : saddr) (n : expr)                  (* [comment removed for export] *)
| KDisj (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)
                                              (* [comment removed for export] *)
| KFill (a : saddr) (n : expr) (c : Z)        (* [comment removed for export] *)
| KUnk (a : saddr) (n : expr).                 (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sidecond : Type :=
| SCBr       (taken : bool) (c : branch_cond) (a b : expr)
| SCFlat     (a : saddr) (n : expr)                     (* [comment removed for export] *)
| SCDisj     (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCInside   (a1 : saddr) (n1 : expr) (a2 : saddr) (n2 : expr)  (* [comment removed for export] *)
| SCStoreOk  (a : saddr) (n : nat)                      (* [comment removed for export] *)
| SCReadBase (a : saddr) (n : nat) (sx : bool) (e : expr)  (* [comment removed for export] *)
| SCEq       (a b : expr).                              (* [comment removed for export] *)

Record sym_state : Type := SSR {
  s_pc   : Z;
  s_regs : list expr;
  s_log  : list sentry;       (* [comment removed for export] *)
  s_know : list kentry;
  s_next : nat;               (* [comment removed for export] *)
  s_resv : option saddr       (* [comment removed for export] *)
}.
End FPX_1.


(* [comment removed for export] *)
Abbreviation SS p r l k n := (SSR p r l k n None).
Section FPX_2. Context {fx : XPropExec.FPState}.


Definition sset : ltac2:(zQ "50!mk4!md!j6!ml1!t2>2ss$0>2rd@1$4@1$1#5>1e$3>3npc$2$0") := ltac2:(zQ "h30!md!ja!ml1!ml9!hk2!lk9!j6!ll5!mm3!mma!mn2!mnc!mo5!mof!mp9!mk4!lm6!lmb!t2\2ss$f\2rd@1$h2@1$0#5\1e$2\3npc$6@6$8^1M1\0$1@1$4$2@3$7@1$0#5^3@3$h0@1$0#5ZKv$5@2$h1@1$0#5Z@1$3^4@3$e@1$3^4@1$9^3^2@1$b^4@1$a^4@1$c^4@1$d^4").

Definition sjump : ltac2:(zQ "20!mk4!j6>2ss$0>3npc$1$0") := ltac2:(zQ "80!j6!mm3!mn2!mnc!mo5!ml9!mof!mk4\2ss$7\3npc$0@6$1^1@1$5^2@1$3^2@1$2^2@1$4^2@1$6^2").

(* [comment removed for export] *)
Definition clr : ltac2:(zQ "10!mk4>2ss$0$0") := ltac2:(zQ "90!ipa!mm3!mn2!mnc!mo5!mq3!ml9!mqb!mk4\2ss$8@6$1@1$5^1@1$6^1@1$3^1@1$2^1@1$4^1@1$0$7").
Definition s_clean : ltac2:(zQ "20!ja!mk4>2ss$1$0") := ltac2:(zQ "70!iob!mqb!ja!hv5!hvc!mof!mk4\2ss$6M0\1x@1$0$1$2@1$5^1\1s$1$3$4").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive rangerel := RInside (delta : Z) | RDisjoint | RPartial | RUnknown.

(* [comment removed for export] *)
Definition rel_lit : ltac2:(zQ "30!j6!ml1!mvf>2rb$1>2rk$0>2rn$0>2kb$1>2kk$0>2kn$0$2") := ltac2:(zQ "e0!ja!j6!jk9!isa!mvf!ml1!jk3!ngb!nh0!nhd!ni8!nj4!nk0!iqe\2rb$5\2rk$1\2rn$1\2kb$5\2kk$1\2kn$1M0\0$0$4@2$c^6^3M0\0$0$4@2$6@2$3^2^5@2$3@2$2^5^4@2$2^2^1@1$9@2$d^5^2M0\0$0$4@2$7@2$3@2$2^5^4^2@2$3@2$2^2^1^5$8$a$b").

Definition elen : ltac2:(zQ "20!h8!ml1>1n$0$1") := ltac2:(zQ "30!h8!nkc!le\1n$0@1$1@1$2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition lit_strip : ltac2:(zQ "30!ml1!js9!j6>1e$0@2$1$0$2") := ltac2:(zQ "83!ml1!j6!jub!h8!huc!ja!ig2!js9&\3op0$4\1a$0\2b0$0@4$2$0$1^7Z&\3op0$6\1a$0\2b0$0@4$2$0$1^7Z&\2op$6\1a$0\1b$0@4$2$0$1^4Z\1e$0M0\1e$0@2$7$0$1^1\1z$1@4$2$0$1^2Z\1n$3@4$2$0$1^2Z\2op$4\1v$0\1b$0M4\2op$4@2$7$0$1^3M0\1b$0@2$7$0$1^1\1c$1@4$2$0$1^3^1\1n$3@4$2$0$1^5Z~0~0~1~1\2sx$5\2lo$3\1n$3\2e0$0@4$2$0$1^8Z\2sx$5\1k$3\1i$1\1n$3@4$2$0$1^8Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z@4$2$0$1^4Z\2op$4\1a$0\1b$0@4$2$0$1^4Z~2~2\2sx$5\2lo$3\1n$3\2e0$0@4$2$0$1^5Z\2sx$5\1k$3\1i$1\1n$3@4$2$0$1^5Z").
Fixpoint find_range (kn : list kentry) (e : expr) : option (Z * Z) :=
  match kn with
  | [] => None
  | KRange e' lo hi :: rest =>
      if expr_eqb e e' then Some (lo, hi) else
      match e with
      | ELit _ => find_range rest e
      | _ =>
        let '(v, c) := lit_strip e in
        let '(v', c') := lit_strip e' in
        if expr_eqb v v' then
          let d := (c - c')%Z in
          if (Z.leb 0 lo && Z.leb lo hi && Z.ltb hi (2 ^ 64) && Z.leb 0 (lo + d) && Z.ltb (hi + d) (2 ^ 64))%bool
          then Some ((lo + d)%Z, (hi + d)%Z) else find_range rest e
        else find_range rest e
      end
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
Lemma zdiv64_eq2 : ltac2:(zQ "50!j6!jge!nl4!nld!pb>1z$0@3$1$0@1$3^1@2$4^1$2"). Proof. exact zdiv64_eq. Qed.

Definition clampi : ltac2:(zQ "20!j6!js9>1r@2$1$0$0@2$1$0$0") := ltac2:(zQ "60!j6!js9!jub!nm7!nn2!nn8\1r@2$1$0$0M1\1r@2$1$0$0@2$1$0$0^1\2lo$0\2hi$0@4$2$0$0@2$4^2Z@2$5^1$3").

(* [comment removed for export] *)
Definition mask_cover : ltac2:(zQ "10!j6>1h$0$0") := ltac2:(zQ "70!ja!j6!jk9!nne!iv4!m7!iqe\1h$1M0\0$0$1@2$4^1ZZ@2$6@2$5+2@1$3@2$2^1+1+1").

Definition lit_shamt : ltac2:(zQ "30!iob!j6!ml1>1e$2@1$0$1") := ltac2:(zQ "a0!ml1!j6!ipa!h8!ja!huc!ig2!iq0!iob!q1\1e$0M0\1e$0@1$8$1^1\1s$1@2$7$1@2$9^1+k0\1n$3@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$5\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2op$6\1a$0\1b$0@1$2$1\2sx$4\2lo$3\1n$3\2e0$0@1$2$1\2sx$4\1k$3\1i$1\1n$3@1$2$1").

(* [comment removed for export] *)
Definition zsigned64 : ltac2:(zQ "10!j6>1v$0$0") := ltac2:(zQ "60!ja!j6!no8!nl4!isa!iqe\1v$1M0\0$0$1@2$4$2^1@2$5^1$3^1").

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

Definition lin_trivial : ltac2:(zQ "20!ja!np2>1l$1$0") := ltac2:(zQ "90!js9!j6!ml1!hk2!ja!hv5!kje!jk3!np2\1l$8M0\1l@2$0$1@1$3@2$0$1$2$4^1\1c$1\2l0@1$3@2$0$1$2M3\2l0@1$3@2$0$1$2$4^1$5\1p@2$0$1$2\2l1@1$3@2$0$1$2M0\1p@2$0$1$2$4^2\1k$1\1e$2M3\2l1@1$3@2$0$1$2$4^3@2$7@2$6^6Z@2$6^2+1\2p0@2$0$1$2\2l2@1$3@2$0$1$2$5").

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
              | Some (lo, hi) =>
                  (* [comment removed for export] *)
                  let q := zdiv64 lo in   (* [comment removed for export] *)
                  if Z.eqb q (zdiv64 hi) then Some ((lo - q * two64)%Z, (hi - q * two64)%Z) else None
              | None => None
              end) with
  | Some r => Some r
  | None =>
  match e with
  | ELit z => let v := zmod64 z in Some (v, v)   (* [comment removed for export] *)
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
          (* [comment removed for export] *)
          match (match b, erange kn a with
                 | ELit m, Some (al, ah) =>
                     let m' := (m mod two64)%Z in
                     let j := Z.log2 (m' + 1) in
                     if (Z.eqb (m' + 1) (2 ^ j) && Z.leb (al / 2 ^ j) (ah / 2 ^ j) && Z.eqb (al / 2 ^ j) (ah / 2 ^ j))%bool
                     then Some ((al mod 2 ^ j)%Z, (ah mod 2 ^ j)%Z)
                     else let jh := Z.log2 (two64 - m') in
                          if (Z.eqb (two64 - m') (2 ^ jh) && Z.ltb jh 64)%bool
                          then Some ((al - al mod 2 ^ jh)%Z, (ah - ah mod 2 ^ jh)%Z)
                          else None
                 | _, _ => None
                 end) with
          | Some r => Some r
          | None =>
          match erange kn a, erange kn b with
          | Some (_, ah), Some (_, bh) => Some (0%Z, Z.min ah bh)
          | Some (_, ah), None => Some (0%Z, ah)
          | None, Some (_, bh) => Some (0%Z, bh)
          | None, None => None
          end
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
            if (Z.leb 0 al && Z.ltb ah (w / 2))%bool then Some (al, ah)
            else if (Nat.leb 1 n && Nat.leb n 8 && Z.leb (w / 2) al && Z.ltb ah w)%bool
                 then Some ((two64 - w + al)%Z, (two64 - w + ah)%Z) else None
        | _, _ => None
        end
      else
        match lo, erange kn a with
        | O, Some (al, ah) =>
            if (Z.leb 0 al && Z.ltb ah w)%bool then Some (al, ah) else Some (0%Z, Z.min (w - 1) (two64 - 1))
        | _, _ => Some (0%Z, Z.min (w - 1) (two64 - 1))
        end
  | EBlob sx k i n =>
      (* [comment removed for export] *)
      if sx then Some (0%Z, two64m1) else Some (0%Z, Z.min (2 ^ (8 * Z.of_nat n) - 1) (two64 - 1))%Z
  end
  end
  end
  end.

(* [comment removed for export] *)
Definition erange_fuel : nat := 64%nat.
End FPX_2.

Global Opaque erange_fuel.
Section FPX_3. Context {fx : XPropExec.FPState}.

(* [comment removed for export] *)
Definition is_factb : ltac2:(zQ "20!ja!np9>1K$1$0") := ltac2:(zQ "80!ml1!mqb!hv5!j6!hvc!np9!h8!ja\1K$5M5\1K$5$7^1\1a$1\1w$6\1v$0$2\1a$1\1n$0$2\1a$1\1n$0\1k$6$2\2lo$3\2hi$3$2\1e$0\1m$3$4\1e$0\2lo$3\2hi$3$4\1a$1\1n$0$4\2a1$1\2n1$0\2a2$1\2n2$0$4\1a$1\1n$0\1c$3$2\1a$1\1n$0$2").
(* [comment removed for export] *)
Fixpoint all_factsb (kn : list kentry) : bool :=
  match kn with [] => true | K :: rest => if is_factb K then all_factsb rest else false end.
Definition facts_of : ltac2:(zQ "20!hk2!np9>2kn@1$0$1@1$0$1") := ltac2:(zQ "60!np9!ja!hk2!nue!nvc!og8\2kn@1$2$0M1\0$1@1$2$0@1$3^1^1@3$5$0$4^1").
Lemma all_factsb_filter : ltac2:(zQ "80!np9!hk2!jge!ja!hvc!nue!nvc!og8>2kn@1$1$0>0@3$2$3@1$5^1$4@3$2@1$1$0@3$7$0$6^2^2").
Proof.
  induction kn as [|K rest IH]; cbn; [reflexivity|].
  destruct (is_factb K); [|discriminate]. intros H. rewrite (IH H). reflexivity.
Qed.
Lemma facts_of_filter : ltac2:(zQ "60!np9!hk2!jge!oh2!nvc!og8>2kn@1$1$0@3$2@1$1$0@1$3^1@3$5$0$4^1").
Proof.
  intros kn. unfold facts_of. destruct (all_factsb kn) eqn:E; [|reflexivity].
  symmetry. apply all_factsb_filter. exact E.
Qed.
Definition erange0 : ltac2:(zQ "60!j6!hk2!iob!js9!ml1!np9>2kn@1$1$5>1e$4@1$2@2$3$0$0") := ltac2:(zQ "60!hk2!oh2!ohe!oia!ml1!np9\2kn@1$0$5\1e$4@3$2$3@1$1^2^1").

(* [comment removed for export] *)
Fixpoint deand (e : expr) : expr * Z :=
  match e with
  | EAlu ALU_AND x (ELit m) =>
      let m' := (m mod two64)%Z in
      let j := Z.log2 (two64 - m') in
      if (Z.eqb (two64 - m') (2 ^ j) && Z.leb j 48)%bool
      then let '(x', s) := deand x in (x', (s + (2 ^ j - 1))%Z)
      else (e, 0%Z)
  | EAlu ALU_ADD a b => let '(a', s1) := deand a in let '(b', s2) := deand b in (EAlu ALU_ADD a' b', (s1 + s2)%Z)
  | _ => (e, 0%Z)
  end.

Definition erange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let r := erange0 kn e in
  let '(e', s) := deand e in
  if Z.eqb s 0 then r else
  match erange0 kn (unlin (lin_of e')) with     (* [comment removed for export] *)
  | Some (lo', hi') =>
      if Z.leb s lo' then
        match r with
        | Some (lo, hi) => Some (Z.max lo (lo' - s), Z.min hi hi')
        | None => Some ((lo' - s)%Z, hi')
        end
      else r
  | None => r
  end.


(* [comment removed for export] *)
Definition base_range : ltac2:(zQ "60!j6!hk2!iob!js9!ml1!np9>2kn@1$1$5>1e$4@1$2@2$3$0$0") := ltac2:(zQ "f2!ml1!j6!oj9!h8!ja!js9!huc!ig2!iq0!hk2!iob!jub!np9!nl4!q1&\2op$6\1a$0\1b$0@2$2^5^4&\2op$7\1a$0\1b$0@2$2^5^4\2kn@1$9$c\1e$0M0\1e$0@1$a@2$5$1$1^1\1z$1=1v$1@2$e^1$d@2$8@2$5$1$1@4$b$1$1^1^1\1n$3@2$2^3^2~0~0~1~1\2sx$4\2lo$3\1n$3\2e0$0@2$2^6^5\2sx$4\1k$3\1i$1\1n$3@2$2^6^5").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ctz_fuel (fuel : nat) (z : Z) : Z :=
  match fuel with
  | O => 0
  | S f => if (Z.eqb (z mod 2) 0)%Z then (1 + ctz_fuel f (z / 2))%Z else 0%Z
  end.
Definition ctz64 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "20!j6!ok3\1z$0@2$1Nk0^1").

(* [comment removed for export] *)
Fixpoint ealign0 (kn : list kentry) (e : expr) {struct e} : Z :=
  match find_align kn e with
  | Some m => if Z.ltb 0 m then ctz64 m else 0%Z
  | None =>
  match e with
  | ELit z => ctz64 (z mod two64)
  | EAlu ALU_ADD a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SUB a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_AND a b => Z.max (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_OR a b => Z.min (ealign0 kn a) (ealign0 kn b)
  | EAlu ALU_SLL a b =>
      match lit_shamt b with
      | Some s => Z.min (ealign0 kn a + s)%Z 64
      | None => 0%Z
      end
  | EMd M_MUL a b => Z.min (ealign0 kn a + ealign0 kn b)%Z 64
  | _ => 0%Z
  end
  end.


(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint lins_e (k : Z) (a : expr) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => if Z.eqb k 0 then [] else [(k, a)]
  | (k', a') :: rest =>
      if expr_eqb a a' then (let s := (k + k')%Z in if Z.eqb s 0 then rest else (s, a') :: rest)
      else (k', a') :: lins_e k a rest
  end.

Definition lsub_e : ltac2:(zQ "40!hk2!js9!j6!ml1>3ts2@1$0@2$1$2$3>3ts1@1$0@2$1$2$3@1$0@2$1$2$3") := ltac2:(zQ "90!j6!ml1!js9!hk2!ju1!ju6!okf!kgb!ir4\3ts2@1$3@2$2$0$1\3ts1@1$3@2$2$0$1@5$7@1$3@2$2$0$1@2$2$0$1\1t@2$2$0$1\3acc@1$3@2$2$0$1@3$6@1$8@3$4$0$1^2@3$5$0$1^2^1^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint find_and_atom_k (sg : Z) (ts : list (Z * expr)) : option (expr * Z) :=
  match ts with
  | [] => None
  | (k, EAlu ALU_AND y (ELit mm)) :: r =>
      if (Z.eqb k sg && Z.ltb 0 mm && Z.eqb (Z.land (mm + 1) mm) 0)%bool then Some (y, mm) else find_and_atom_k sg r
  | _ :: r => find_and_atom_k sg r
  end.

Definition pageup_low_k : ltac2:(zQ "30!j6!iob!ml1>2sg$0>1e$2>1m$0@1$1$0") := ltac2:(zQ "hb0!j6!ml1!js9!hk2!iob!ju6!ipa!ju1!jk9!jk3!ja!okf!np2!ol9!q1!l8!iq0!om3!ome!nkc!on6!nl4!kgb!kje!isa!iv4!ir4\2sg$0\1e$1\1m$0=1l$c@1$d^2M4\1x@1$4@2$2$1$0@1$4$0@2$h4^4@3$5$0@1$3@2$2$0$1^1\1p@2$2$1$0M2\1p@2$2$1$0@1$4$0^1\1y$1\2mm$0Ma\0$a@1$4$0@2$9@2$9@2$h9Z^5@2$h7@2$e@2$8^1+1^5Z@2$h8@2$8^1+1$h5=2ly$c@1$d^2=4rest@1$3@2$2$0$1@3$b@1$ha^8@3$h2$h1^3@1$h3^2@3$5$0@1$3@2$2$0$1^5M3\1x@1$3@2$2$0$1@1$4$0@5$h6@1$3@2$2$0$1@2$2$0$1\1t@2$2$0$1\3acc@1$3@2$2$0$1@3$b@2$f^b@3$7$0$1^2@3$5$0$1^2^1@3$5$0@1$3@2$2$0$1^2^1@2$h0$0@2$e@2$8@3$7$0@1$3@2$2$0$1^6@2$f^9@3$7$0@1$3@2$2$0$1^2^7\1p@2$2$0$1\2l0@1$3@2$2$0$1@1$6$0@1$6$0@1$6$0").

(* [comment removed for export] *)
Definition pageup_low : ltac2:(zQ "30!j6!iob!ml1>1e$2>1m$0@1$1$0") := ltac2:(zQ "50!j6!iob!oo9!iq0!ml1\1e$4\1m$0M1\1x@1$1$0@1$1$0@3$2+1^2^1\1r$0@2$3$0^1@3$2-1^2^1").

Definition pageup_align : ltac2:(zQ "20!j6!ml1>1e$1$0") := ltac2:(zQ "h30!j6!ml1!js9!iob!ja!hk2!ju6!op9!on6!iq0!jk3!oq4!oqd!np2!ol9!jk9!kje!isa!m7\1e$1=1l$d@1$e^1M3\1x@1$3@2$2$1$0$0M3\1x@1$3@2$2$1$0@1$3@2$2$1$0@2$8+1@3$6$0@1$5@2$2$0$1^1\1p@2$2$1$0@2$9@2$2$1$0^1@2$8-1@3$6$0@1$5@2$2$0$1^1\1p@2$2$1$0M2\1p@2$2$1$0$0^1\1y$1\2mm$0=1m$0@2$f^1+1=1k$0@1$b^1M4\0$4$0@2$a@2$h0^2@2$h2+2^1@2$h1^1+k0M3\1x@1$3$0$0@2$c^7^2\1z$0M0\1z$0$0^1^2\1p$7Z\1p$7ZZZZ").

Definition ealign : ltac2:(zQ "40!hk2!j6!ml1!np9>2kn@1$0$3>1e$2$1") := ltac2:(zQ "70!hk2!orb!oh2!os6!ml1!np9!nn2\2kn@1$0$5\1e$4@2$6@2$1@1$2^2^1@1$3^1").

(* [comment removed for export] *)
Definition lin_nowrap : ltac2:(zQ "40!ja!hk2!ml1!np9>2kn@1$1$3>1e$2$0") := ltac2:(zQ "h20!j6!js9!hk2!ml1!ja!iob!jk3!hv5!ju1!ju6!oj9!np9!np2!ol9!ot6!nl4!isa!iv4\2kn@1$2$b\1e$3=1l$c@1$d^1M5\1x@1$5@2$1$0$0$4@3$e@1$a^3@3$8$0@1$2@2$1$0$3^1@3$9$0@1$2@2$1$0$3^1\1p@2$1$0$0M1\1p@2$1$0$0$4^1\2lo$0\2hi$0@2$6@2$h0Z^2@2$h1^1$f$7").

(* [comment removed for export] *)
Definition srl_rem : ltac2:(zQ "20!ml1!j6>1e$0>1m$1$0") := ltac2:(zQ "60!j6!om3!ome!nkc!ml1!iqe\1e$4\1m$0@3$2$1^2@1$3@2$5^1+1").

(* [comment removed for export] *)
Definition highmask_s : ltac2:(zQ "20!j6!iob>2mk$0@1$1$0") := ltac2:(zQ "d0!j6!nl4!jk3!ja!iv4!iqe!ipa!iq0!iob!kje!ou3!q1!m7\2mk$0=2m'$0@2$b^1$1=1s$0@1$a@2$5$1^1M3\0$3@1$8$0@2$2@2$2@2$9@2$5$1^2@2$c+2^1@2$4Z^1@2$4^1+k0@2$7$0^1@1$6$0").

Fixpoint srl_expand (kn : list kentry) (ts : list (Z * expr)) : Z * list (Z * expr) :=
  match ts with
  | [] => (0%Z, [])
  | (k, a) :: rest =>
      let '(c, ts') := srl_expand kn rest in
      let keep := (c, lins_e k a ts') in
      match a with
      | EAlu ALU_SRL e (ELit s) =>
          let m := (2 ^ ((s mod two64) mod 64))%Z in
          if (Z.eqb (k mod m)%Z 0%Z && lin_nowrap kn e)%bool then
            let q := (k / m)%Z in
            let le := lin_of e in
            if Z.leb ((s mod two64) mod 64) (ealign kn e) then   (* [comment removed for export] *)
              ((c + q * fst le)%Z, fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le))
            else
            ((c + q * fst le)%Z,
             lins_e (- q)%Z (srl_rem e m) (fold_right (fun t acc => lins_e (q * fst t)%Z (snd t) acc) ts' (snd le)))
          else keep
      | EAlu ALU_AND e (ELit mk) =>
          (* [comment removed for export] *)
          match highmask_s mk with
          | Some s =>
              if lin_nowrap kn e then
                let le := lin_of e in
                ((c + k * fst le)%Z,
                 lins_e (- k)%Z (srl_rem e (2 ^ s)) (fold_right (fun t acc => lins_e (k * fst t)%Z (snd t) acc) ts' (snd le)))
              else keep
          | None => keep
          end
      | _ => keep
      end
  end.

(* [comment removed for export] *)
Fixpoint has_srl (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => false
  | (_, EAlu ALU_SRL _ (ELit _)) :: _ => true
  | _ :: rest => has_srl rest
  end.
(* [comment removed for export] *)
Definition sfact : ltac2:(zQ "00T") := ltac2:(zQ "40!js9!j6!hk2!ml1@2$0@1$2@2$0$1$3@2$0$1$1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sum_fact_x (allkn : list kentry) (ts : list (Z * expr)) (lo hi : Z) : list sfact :=
  let '(c2, ts2) := srl_expand allkn ts in
  match ts2 with
  | _ :: _ => if Z.eqb c2 0 then [] else [(ts2, ((lo - c2)%Z, (hi - c2)%Z))]
  | [] => []
  end.

(* [comment removed for export] *)
Definition fact_nowrap : ltac2:(zQ "50!ja!hk2!j6!ml1!np9>5allkn@1$1$4>1e$3>2hi$2$0") := ltac2:(zQ "h20!j6!js9!hk2!ml1!ja!iob!nl4!iv4!jk3!hv5!ju1!ju6!oj9!np9!np2!ol9!ot6!jk9\5allkn@1$2$d\1e$3\2hi$0=1l$e@1$f^2M5\1x@1$5@2$1$0$0$4@3$h0@1$c^4@3$a$0@1$2@2$1$0$3^1@3$b$0@1$2@2$1$0$3^1\1p@2$1$0$0M1\1p@2$1$0$0$4^1\1a$0\1b$0@2$8@2$7^1$6@2$7^5@2$h1^2$6$9").

Fixpoint sum_facts (allkn kn : list kentry) : list sfact :=
  match kn with
  | [] => []
  | KRange e lo hi :: rest =>
      match e with
      | EVar _ => sum_facts allkn rest
      | _ =>
        match lin_of e with
        | (c, (_ :: _ :: _) as ts) =>
            if fact_nowrap allkn e hi then (ts, ((lo - c)%Z, (hi - c)%Z)) :: sum_fact_x allkn ts (lo - c)%Z (hi - c)%Z ++ sum_facts allkn rest
            else sum_facts allkn rest
        | _ => sum_facts allkn rest
        end
      end
  | _ :: rest => sum_facts allkn rest
  end.

(* [comment removed for export] *)
Fixpoint coef_of (a : expr) (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, a') :: r => if expr_eqb a a' then k else coef_of a r
  end.

(* [comment removed for export] *)
Fixpoint fact_quot (fts ts : list (Z * expr)) (acc : option Z) : option Z :=
  match fts with
  | [] => acc
  | (k, a) :: r =>
      if Z.eqb k 0 then None else
      let K := coef_of a ts in
      if Z.eqb K 0 then None else
      if negb (Z.eqb (K mod k) 0) then None else
      let q := (K / k)%Z in
      match acc with
      | None => fact_quot r ts (Some q)
      | Some q0 => if Z.eqb q0 q then fact_quot r ts acc else None
      end
  end.

Definition sub_fact : ltac2:(zQ "40!j6!hk2!js9!ml1>1q$0>3fts@1$1@2$2$0$3>2ts@1$1@2$2$0$3@1$1@2$2$0$3") := ltac2:(zQ "a0!j6!ml1!js9!hk2!ju1!ju6!okf!kgb!l8!ir4\1q$0\3fts@1$3@2$2$0$1\2ts@1$3@2$2$0$1@5$7@1$3@2$2$0$1@2$2$0$1\1t@2$2$0$1\3acc@1$3@2$2$0$1@3$6@1$9@2$8^5@3$4$0$1^2@3$5$0$1^2^1^1^2").

(* [comment removed for export] *)
Fixpoint sum_subst (fs : list sfact) (ts : list (Z * expr)) (lo hi : Z) (hit : bool)
  : list (Z * expr) * (Z * Z) * bool :=
  match fs with
  | [] => (ts, (lo, hi), hit)
  | (fts, (flo, fhi)) :: r =>
      match fact_quot fts ts None with
      | Some q =>
          let ts' := sub_fact q fts ts in
          if Z.leb 0 q then sum_subst r ts' (lo + q * flo)%Z (hi + q * fhi)%Z true
          else sum_subst r ts' (lo + q * fhi)%Z (hi + q * flo)%Z true
      | None => sum_subst r ts lo hi hit
      end
  end.

Definition lin_test_rel : ltac2:(zQ "60!j6!ja!hk2!js9!ml1!np9>2kn@1$2$5>1c$0>2ts@1$2@2$3$0$4>4test>0$0>0$0$1$1") := ltac2:(zQ "f1!j6!js9!ja!hk2!ml1!hv5!oua!iob!jk9!ov3!oj9!ov9!pg6!np9!ot6&@2$1@1$3@2$1$0$4@2$1$0$0\2kn@1$3$d\1c$0\2ts@1$3@2$1$0$4\4test>0$0>0$0$2M3\1x@1$3$6$2@2$b^4^4$5\1s$6\1l@1$3$6M1\1x@2$1~0$2$2@5$c@3$9$6^2^1^4ZZ$5\1p~0\1b$2M1\1p~0$2^2\3ts'@1$3@2$1$0$4\2p0@2$1$0$0M1\2p0@2$1$0$0$2^1\3lo0$0\3hi0$0M2\1b$2$2^5M7\1x@1$7@2$1$0$0$2@3$e@1$a^c^b^4\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0@2^c@2$8^2^5@2$8^1^4$5$5").

Definition lin_test : ltac2:(zQ "60!j6!ja!hk2!js9!ml1!np9>2kn@1$2$5>1c$0>2ts@1$2@2$3$0$4>4test>0$0>0$0$1$1") := ltac2:(zQ "b0!j6!ja!js9!hk2!iob!ph3!hvc!oj9!ml1!np9!ot6\2kn@1$3$9\1c$0\2ts@1$3@2$2$0$8\4test>0$0>0$0$1M4\1x@1$4@2$2$0$0$1@3$a@1$7^4^3^2\1p@2$2$0$0M2\1p@2$2$0$0$1^1\2lo$0\2hi$0M1\0$1$1@2^4^2^1$6@4$5^7^6^5^4@4$5^4^3^2^1").

(* [comment removed for export] *)
Fixpoint srl_scale_need (ts : list (Z * expr)) : Z :=
  match ts with
  | [] => 0
  | (k, EAlu ALU_SRL _ (ELit s)) :: rest => Z.max (((s mod two64) mod 64) - ctz64 k)%Z (srl_scale_need rest)
  | _ :: rest => srl_scale_need rest
  end.
Definition zcdiv : ltac2:(zQ "10!j6>1a$0>1b$0$0") := ltac2:(zQ "30!j6!ir4!pb\1a$0\1b$0@1$1@2$2@1$1^2^1").
Definition lin_srange (kn : list kentry) (e : expr) : option (Z * Z) :=
  let l := lin_of e in
  let j := srl_scale_need (snd l) in
  if (if Z.leb 0 j then Z.leb j 24 else false) then   (* [comment removed for export] *)
    let sc := (2 ^ j)%Z in
    let ts := List.map (fun t => ((sc * fst t)%Z, snd t)) (snd l) in
    let '(c2, t2) := srl_expand kn ts in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    match lin_range (erange kn) (sc * fst l + c2 + c3)%Z t3 with
    | Some (lo', hi') =>
        let lo := zcdiv lo' sc in let hi := (hi' / sc)%Z in
        if (if Z.leb 0 lo then (if Z.leb lo hi then Z.ltb hi two64 else false) else false) then Some (lo, hi) else None
    | None => None
    end
  else None.

(* [comment removed for export] *)
Definition lin_nowrapR (kn : list kentry) (e : expr) : bool :=
  let l := lin_of e in
  let '(c2, t2) := srl_expand kn (snd l) in            (* [comment removed for export] *)
  if lin_test kn (fst l + c2)%Z t2 (fun lo hi => (Z.leb 0 lo && Z.ltb hi two64)%bool) then true
  else (* [comment removed for export] *)
    match lin_srange kn e with Some _ => true | None => false end.

(* [comment removed for export] *)
Fixpoint mentions_var (v : nat) (e : expr) : bool :=
  match e with
  | ELit _ => false
  | EVar w => Nat.eqb v w
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if mentions_var v a then true else mentions_var v b
  | EExt _ _ _ a => mentions_var v a
  | EBlob _ _ _ _ => false
  end.
Fixpoint shares_var (e1 e2 : expr) : bool :=
  match e2 with
  | ELit _ => false
  | EVar w => mentions_var w e1
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if shares_var e1 a then true else shares_var e1 b
  | EExt _ _ _ a => shares_var e1 a
  | EBlob _ _ _ _ => false
  end.
Fixpoint novars (e : expr) : bool :=
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if novars a then novars b else false
  | EExt _ _ _ a => novars a
  | EBlob _ _ _ _ => true
  end.
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition lin_apart0 : ltac2:(zQ "50!j6!ml1!ja!hk2!np9>2kn@1$3$4>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2") := ltac2:(zQ "h20!j6!ml1!hk2!js9!jk3!ju1!ju6!pi3!np2!ol9!isa!iqe!ngb!pj2!pje!np9!jk9!ir4\2kn@1$2$f\2b1$1\2k1$0\2n1$0\2b2$1\2k2$0\2n2$0@2$4@2$4@2$7^7^6@2$7^7^3=2l1$8@1$9^6=2l2$8@1$9^4@4$d^9@2$b@2$b@2$h0@3$5$0@1$2@2$3$0$1^1^4@3$5$0@1$2@2$3$0$1^2^7@2$e@3$6$0@1$2@2$3$0$1^1@3$6$0@1$2@2$3$0$1^2\2lo$0\2hi$0@2$c@2$a^8^2@2$a^1@1$h1^5").
Definition lin_apart : ltac2:(zQ "50!j6!ml1!ja!hk2!np9>2kn@1$3$4>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2") := ltac2:(zQ "80!j6!ja!ml1!hv5!hk2!pk8!pl6!np9\2kn@1$4$7\2b1$2\2k1$0\2n1$0\2b2$2\2k2$0\2n2$0M1\0$1$1@2$6^6^3@7$5^7^6^5^4^3^2^1$3").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zlit64 : ltac2:(zQ "10!j6>1z$0$0") := ltac2:(zQ "70!ja!j6!nl4!jk3!isa!iv4!q1\1z$1M0\0$0$1@2$3@2$4Z^1@2$5^1$2^1@2$6^1$2").

(* [comment removed for export] *)
Definition lin_brange : ltac2:(zQ "60!j6!hk2!iob!js9!ml1!np9>2kn@1$1$5>1e$4@1$2@2$3$0$0") := ltac2:(zQ "ha1!j6!js9!hk2!iob!ml1!ja!ipa!oua!jk9!iq0!jk3!ov3!hv5!ju1!jub!ju6!oj9!ov9!pg6!np9!np2!ol9!ot6!nl4!isa!iv4&@2$1@1$2@2$1$0$4@2$1$0$0\2kn@1$2$h3\1e$4=1l$h4@1$h5^1M2\1x@1$2$7@1$3@2$1$0$0@2$h1^3^3@1$6@2$1$0$0\1s$7\2l0@1$2$7M1\1x@2$1~0$5@1$3@2$1$0$0@5$h2@3$b$7^2^1@3$f$0@1$2@2$1$0$4^3ZZ$c\1p~0\1b$5M1\1p~0@1$3@2$1$0$0^2\3ts'@1$2@2$1$0$4\2p0@2$1$0$0M1\2p0@2$1$0$0@1$3@2$1$0$0^1\3lo0$0\3hi0$0M5\1b$5@1$3@2$1$0$0^5M3\1x@1$3@2$1$0$0@1$3@2$1$0$0@3$h6@1$h0^b@3$d$0@1$2@2$1$0$4^9^4\1p@2$1$0$0M1\1p@2$1$0$0@1$3@2$1$0$0^1\2lo$0\2hi$0=3lo'$0@2$8^2^5=3hi'$0@2$8^2^5M5\0$5@1$3@2$1$0$0@2$a@2$h8Z^2@2$h9^1$h7@2$9@2$1$0$0@4$e$0$0^2^1@1$6@2$1$0$0@1$6@2$1$0$0@1$6@2$1$0$0").

Definition xlo : ltac2:(zQ "50!hk2!iob!j6!ml1!np9>2kn@1$0$4>1e$3@1$1$2") := ltac2:(zQ "h0c!j6!iob!js9!iq0!ml1!ipa!oj9!pm4!pn2!h8!ja!huc!ig2!hk2!po0!np9&M2\1p@2$2$0$0@1$1$0^1\2lo$0\1z$0@2$3$0^2&\1p@2$2$0$0~0&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~1~2&M1\1x@1$1@2$2$0$0@1$1$0@2$6^5^4~1~3&\1b$4~4&\1a$4~5&\2op$b~6&\2op$c~6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~1~9&M1\1x@1$1@2$2$0$0@1$1$0@2$6^6^5~1~a\2kn@1$d$f\1e$4M4\1e$4@1$1$0^1\1z$0@2$3$0@1$e^1\1n$9M1\1x@1$1@2$2$0$0@1$1$0@2$6^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~1@1$5$0~7~7~8~8\2sx$a\2lo$9\1n$9\2e0$4~b\2sx$a\1k$9\1i$0\1n$9~b").
Definition xhi : ltac2:(zQ "50!hk2!iob!j6!ml1!np9>2kn@1$0$4>1e$3@1$1$2") := ltac2:(zQ "h0c!j6!iob!js9!iq0!ml1!ipa!oj9!pm4!pn2!h8!ja!huc!ig2!hk2!po0!np9&M2\1p@2$2$0$0@1$1$0^1\1z$0\2hi$0@2$3$0^1&\1p@2$2$0$0~0&M1\1x@1$1@2$2$0$0@1$1$0@2$8^5^4~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$7^5^4~1~2&M1\1x@1$1@2$2$0$0@1$1$0@2$6^5^4~1~3&\1b$4~4&\1a$4~5&\2op$b~6&\2op$c~6&M1\1x@1$1@2$2$0$0@1$1$0@2$8^6^5~1@1$5$0&M1\1x@1$1@2$2$0$0@1$1$0@2$7^6^5~1~9&M1\1x@1$1@2$2$0$0@1$1$0@2$6^6^5~1~a\2kn@1$d$f\1e$4M4\1e$4@1$1$0^1\1z$0@2$3$0@1$e^1\1n$9M1\1x@1$1@2$2$0$0@1$1$0@2$6^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$7^3^2~1M1\1x@1$1@2$2$0$0@1$1$0@2$8^3^2~1@1$5$0~7~7~8~8\2sx$a\2lo$9\1n$9\2e0$4~b\2sx$a\1k$9\1i$0\1n$9~b").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition xterms : ltac2:(zQ "00S") := ltac2:(zQ "40!hk2!js9!j6!ml1@1$0@2$1$3$2").

Fixpoint xt_nowrap (kn : list kentry) (ts : xterms) : bool :=
  match ts with [] => true | (e, _) :: r => lin_nowrapR kn e && xt_nowrap kn r end.
Fixpoint xt_const (ts : xterms) : Z :=
  match ts with [] => 0 | (e, k) :: r => (fst (lin_of e) + k + xt_const r)%Z end.
Fixpoint xt_lin (ts : xterms) : list (Z * expr) :=
  match ts with [] => [] | (e, _) :: r => fold_right (fun t acc => lins_e (fst t) (snd t) acc) (xt_lin r) (snd (lin_of e)) end.

(* [comment removed for export] *)
Definition lin_ge0_scaled (kn : list kentry) (c : Z) (ts : list (Z * expr)) : bool :=
  let j := srl_scale_need ts in
  if (if Z.ltb 0 j then Z.leb j 24 else false) then
    let sc := (2 ^ j)%Z in
    let ts' := List.map (fun t => ((sc * fst t)%Z, snd t)) ts in
    let '(c2, t2) := srl_expand kn ts' in
    let '(c3, t3) := (if has_srl t2 then srl_expand kn t2 else (0%Z, t2)) in
    lin_test kn (sc * c + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
  else false.

(* [comment removed for export] *)
Definition lin_ge0 (kn : list kentry) (pos neg : xterms) : bool :=
  (xt_nowrap kn pos && xt_nowrap kn neg &&
   (* [comment removed for export] *)
   (if lin_test kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg)) (fun lo _ => Z.leb 0 lo) then true
    else let '(c2, t2) := srl_expand kn (lsub_e (xt_lin pos) (xt_lin neg)) in
         if lin_test kn (xt_const pos - xt_const neg + c2)%Z t2 (fun lo _ => Z.leb 0 lo) then true
         else (* [comment removed for export] *)
         if (if has_srl t2 then
               let '(c3, t3) := srl_expand kn t2 in
               lin_test kn (xt_const pos - xt_const neg + c2 + c3)%Z t3 (fun lo _ => Z.leb 0 lo)
             else false) then true
         else (* [comment removed for export] *)
           lin_ge0_scaled kn (xt_const pos - xt_const neg)%Z (lsub_e (xt_lin pos) (xt_lin neg))))%bool.

(* [comment removed for export] *)
Definition xinside0 : ltac2:(zQ "50!ml1!j6!ja!hk2!np9>2kn@1$3$4>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2") := ltac2:(zQ "b0!ml1!j6!js9!ov3!jub!poa!ja!pof!hv5!hk2!np9\2kn@1$9$a\2b1$0\2k1$1\2n1$0\2b2$0\2k2$1\2n2$0M6\0$6$6@3$7^7@3$3@2$2$0$1@4$4$0$1^6^5@1$5@2$2$0$1@3$3@2$2$0$1@4$4$0$1^3^2@1$5@2$2$0$1@3$7^7@3$3@2$2$0$1@4$4$0$1^3^2@3$3@2$2$0$1@4$4$0$1^1Z@1$5@2$2$0$1@3$3@2$2$0$1@4$4$0$1^6^5@3$3@2$2$0$1@4$4$0$1^4Z@1$5@2$2$0$1$8").
(* [comment removed for export] *)
Definition xinside_num : ltac2:(zQ "50!ml1!j6!ja!hk2!np9>2kn@1$3$4>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2") := ltac2:(zQ "f0!j6!iob!ja!hv5!jk9!js9!ml1!ppa!pq1!isa!jk3!hk2!pq8!np9!kje\2kn@1$b$d\2b1$6\2k1$0\2n1$6\2b2$6\2k2$0\2n2$6M1\1x@1$1$0$2@2$8^7^3\3lo2$0M1\1x@1$1$0$2@2$7^8^4\3hi2$0M2\0$2$2@2$e^2^1M1\1x@1$1@2$5$0$0$2@2$c^9^8\1p@2$5$0$0M5\1p@2$5$0$0$2^1\3lo1$0\3hi1$0M1\1x@1$1$0$2@2$7^c^9\2h1$0M1\1x@1$1$0$2@2$8^d^7\2l2$0@2$a@2$9@2$4^7^9@2$4^4^c@2$9@2$4@2$4^3^c^2@2$4@2$4^7^9^1$3$3$3$3$3$3").
Definition xinside : ltac2:(zQ "50!ml1!j6!ja!hk2!np9>2kn@1$3$4>2b1$0>2k1$1>2n1$0>2b2$0>2k2$1>2n2$0$2") := ltac2:(zQ "a0!ja!ml1!j6!hv5!hk2!pr6!pl6!ps0!psc!np9\2kn@1$4$9\2b1$1\2k1$2\2n1$1\2b2$1\2k2$2\2n2$1M0\0$0$0@2$6^6^3@7$7^7^6^5^4^3^2^1M0\0$0$0@1$5^3@7$8^7^6^5^4^3^2^1$3").


(* [comment removed for export] *)
Definition sub_itv : ltac2:(zQ "60!j6!ml1!ja!hk2!np9!mqb>5allkn@1$3$4>1b$1>1k$0>1n$0>1c$5>1m$1$2") := ltac2:(zQ "h40!ja!j6!hv5!ptb!isa!jk3!iob!pu4!ml1!jk9!hk2!hvc!nkc!pue!pq1!nk0!np9!mqb!nl4!iv4\5allkn@1$a$h0\1b$8\1k$1\1n$1\1c$h1\1m$8M0\0$0$0M0\0$0$0@2$5@2$f^5@1$7^2@2$4@1$3^2^4M6\1x@1$6$1$0@2$e^6^1\2ml$1@2$4@2$9^5^4@2$9@1$3^3^1$2$2$bM0\0$0$0@2$5@2$4Z^3@2$h3^3$h2@7$d^6^5^4@1$c^3@1$7^2@1$3^2^1$2").

(* [comment removed for export] *)
Fixpoint kdisj_apart (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) (b2 : expr) (k2 n2 : Z) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv allkn b1 k1 n1 c1 m1 then sub_itv allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv allkn b1 k1 n1 c2 m2 then sub_itv allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart allkn rest b1 k1 n1 b2 k2 n2
  end.

Definition ranges_apart : ltac2:(zQ "50!j6!ml1!ja!hk2!np9>2kn@1$3$4>2b1$1>2k1$0>2n1$0>2b2$1>2k2$0>2n2$0$2") := ltac2:(zQ "f0!j6!ja!js9!jk9!iob!hv5!hvc!pq8!ml1!isa!hk2!ngb!pv9!qg8!np9\2kn@1$a$e\2b1$8\2k1$0\2n1$0\2b2$8\2k2$0\2n2$0M1\0$1$1M4\1x@1$4@2$2$0$0$1@2$7^7^6\1p@2$2$0$0M2\1p@2$2$0$0$1^1\3lo1$0\3hi1$0M4\1x@1$4@2$2$0$0$1@2$7^a^6\2p0@2$2$0$0M2\2p0@2$2$0$0$1^1\3lo2$0\3hi2$0@2$b@2$9@2$3@2$3^4^b^a@2$3^2^8@2$9@2$3@2$3^1^8^7@2$3^5^b$5$5$6M1\0$1$1@8$c^7^7^6^5^4^3^2^1$6@7$d^7^6^5^4^3^2^1").

Definition sub_itv_x : ltac2:(zQ "60!ml1!ja!hk2!j6!np9!mqb>2kn@1$2$4>1b$0>1k$3>1n$0>1c$5>1m$0$1") := ltac2:(zQ "80!ml1!hk2!j6!pue!pu4!ptb!np9!mqb\2kn@1$1$6\1b$0\1k$2\1n$0\1c$7\1m$0@7$3^6^5^4^3@1$4^2@1$5^2^1").

Fixpoint kdisj_apart_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match kn with
  | [] => false
  | KDisj c1 m1 c2 m2 :: rest =>
      if (if sub_itv_x allkn b1 k1 n1 c1 m1 then sub_itv_x allkn b2 k2 n2 c2 m2 else false) then true
      else if (if sub_itv_x allkn b1 k1 n1 c2 m2 then sub_itv_x allkn b2 k2 n2 c1 m1 else false) then true
      else kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  | _ :: rest => kdisj_apart_x allkn rest b1 k1 n1 b2 k2 n2
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition end_hi : ltac2:(zQ "50!j6!ml1!hk2!iob!np9>2kn@1$2$4>1b$1>1k$0>1n$1>3lo1$0>3hi1$0>2h1$0@1$3$0") := ltac2:(zQ "h6e!j6!ja!iob!js9!jk9!ipa!kkd!qh5!ml1!iq0!hv5!nkc!oh2!qhe!nl4!isa!iv4!h8!huc!ig2!hk2!np9&M3\1p@2$3$0$0@1$2$0^1\1z$0\3ehi$0@2$9$0^1&\1p@2$3$0$0~0&M1\0$1$1@2$fZ@2$4^6^8@2$h0@2$4@2$4^5^8^4$e$a&@2$d@1$c^a@3$7$6@3$7$6^9@1$b^8^7&M2\1x@1$2@2$3$0$0@1$2$0~3~1@1$5$0&M1\0$1@1$2$0~2~4@1$5$0&\2b0$8~5&\1a$8~6&\2op$h2~7&\2op$h3~7&M1\0$1$1@2$fZ@2$4^7^9@2$h0@2$4@2$4^6^9^5$e$a&@2$d@1$c^b@3$7$6@3$7$6^a@1$b^9^8&M2\1x@1$2@2$3$0$0@1$2$0~b~1@1$5$0&M1\0$1@1$2$0~a~c@1$5$0\2kn@1$h4$h5\1b$8\1k$0\1n$8\3lo1$0\3hi1$0\2h1$0M8\1n$8@1$2$0^4\1z$0@1$5$0\2n0$h1M1\0$1@1$2$0M1\0$1$1@2$fZ@2$4^4^6@2$h0@2$4@2$4^3^6^2$e$aM2\1x@1$2@2$3$0$0@1$2$0@2$d@1$c^8@3$7$6@3$7$6^7@1$b^6^5~1@1$5$0@1$5$0~8~8~9~9\2sx$1\2lo$h1\2n0$h1\1e$8~d\2sx$1\2k0$h1\1i$0\2n0$h1~d").

Definition ranges_apart_x (kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 => ranges_apart kn b1 k1 (zlit64 z1) b2 k2 (zlit64 z2)
  | _, _ =>
    if (match base_range kn b1, base_range kn b2, xhi kn n1, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if kdisj_apart_x kn kn b1 k1 n1 b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Record sprep := SPrep {
  sp_rng : option (Z * Z);          (* [comment removed for export] *)
  sp_h1 : option Z;                 (* [comment removed for export] *)
  sp_D : list (saddr * expr);       (* [comment removed for export] *)
  sp_Dx : list (saddr * expr) }.    (* [comment removed for export] *)

Fixpoint disj_sides (allkn kn : list kentry) (b1 : expr) (k1 n1 : Z) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides allkn rest b1 k1 n1 in
      let r1 := if sub_itv allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides allkn rest b1 k1 n1
  end.

Fixpoint disj_sides_x (allkn kn : list kentry) (b1 : expr) (k1 : Z) (n1 : expr) : list (saddr * expr) :=
  match kn with
  | [] => []
  | KDisj c1 m1 c2 m2 :: rest =>
      let r := disj_sides_x allkn rest b1 k1 n1 in
      let r1 := if sub_itv_x allkn b1 k1 n1 c2 m2 then (c1, m1) :: r else r in
      if sub_itv_x allkn b1 k1 n1 c1 m1 then (c2, m2) :: r1 else r1
  | _ :: rest => disj_sides_x allkn rest b1 k1 n1
  end.

Fixpoint in_sides (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 n2 : Z) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv allkn b2 k2 n2 c m then true else in_sides allkn r b2 k2 n2
  end.

Fixpoint in_sides_x (allkn : list kentry) (D : list (saddr * expr)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match D with
  | [] => false
  | (c, m) :: r => if sub_itv_x allkn b2 k2 n2 c m then true else in_sides_x allkn r b2 k2 n2
  end.

Definition mk_sprep : ltac2:(zQ "50!ml1!hk2!j6!qld!np9>2kn@1$1$4>2b1$0>2k1$2>2n1$0$3") := ltac2:(zQ "h12!ml1!js9!mqb!poa!h8!j6!ja!hk2!huc!ig2!qm6!pq8!qmf!qnd!ppa!po0!np9&\2op$8\1a$0\1b$0@1$3@2$1$2$0&\2op$9\1a$0\1b$0@1$3@2$1$2$0\2kn@1$7$h0\2b1$0\2k1$5\2n1$0@4$a@2$b^4^3@2$e^4^1M0\2n1$0@1$7@2$1$2$0^1\2z1$5@5$c^5^5^4^3@1$f^1\1n$4@1$3@2$1$2$0~0~0~1~1\2sx$6\2lo$4\1n$4\1e$0@1$3@2$1$2$0\2sx$6\1k$4\1i$5\1n$4@1$3@2$1$2$0@5$d^4^4^3^2^1").

(* [comment removed for export] *)
Definition ranges_apart_p (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, base_range kn b2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides kn (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, base_range kn b2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive ptree (A : Type) : Type := PTLeaf | PTNode (l : ptree A) (o : option A) (r : ptree A).
End FPX_3.

Arguments PTLeaf {A}. Arguments PTNode {A} _ _ _.
Section FPX_4. Context {fx : XPropExec.FPState}.

Fixpoint pt_get {A} (t : ptree A) (k : positive) {struct k} : option A :=
  match t with
  | PTLeaf => None
  | PTNode l o r => match k with xH => o | xO k' => pt_get l k' | xI k' => pt_get r k' end
  end.
Fixpoint pt_set {A} (k : positive) (v : A) (t : ptree A) {struct k} : ptree A :=
  match t with
  | PTLeaf => match k with
              | xH => PTNode PTLeaf (Some v) PTLeaf
              | xO k' => PTNode (pt_set k' v PTLeaf) None PTLeaf
              | xI k' => PTNode PTLeaf None (pt_set k' v PTLeaf)
              end
  | PTNode l o r => match k with
                    | xH => PTNode l (Some v) r
                    | xO k' => PTNode (pt_set k' v l) o r
                    | xI k' => PTNode l o (pt_set k' v r)
                    end
  end.
Lemma pt_gss : ltac2:(zQ "70!iq0!iob!jge!op9!qt8!qu2!quc>1AT>1k$3>1v^2>1t@1$6^3@3$2@1$1^4@3$4^4@4$5^4^3^2^1^3@2$0^4^2").
Proof. induction k; destruct t; cbn; auto. Qed.
Lemma pt_gso : ltac2:(zQ "70!op9!jge!qt8!iob!qv5!qu2!quc>1AT>1k$0>2k'$0>1v^3>1t@1$6^4>0@1$4@3$1$0^4^3@3$1@1$3^6@3$2^6@4$5^6^4^3^2^5@3$2^6^2^5").
Proof.
  induction k; destruct k', t; cbn; intros; auto;
    try (rewrite IHk by congruence); try (destruct k; reflexivity); try reflexivity; congruence.
Qed.
Lemma pt_get_leaf : ltac2:(zQ "60!ipa!iob!jge!op9!qt8!qvc>1AT>1k$3@3$2@1$1^2@3$4^2@1$5^2^1@1$0^2").
Proof. destruct k; reflexivity. Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive lres :=
| LHit (v : expr) (scs : list sidecond) (hints : list bool)
| LMiss (scs : list sidecond) (hints : list bool)     (* [comment removed for export] *)
| LStuck.

Fixpoint zbytes_le_to_Z (bs : list Z) : Z :=
  match bs with
  | [] => 0
  | b :: rest => Z.lor b (Z.shiftl (zbytes_le_to_Z rest) 8)
  end.

Definition lit_of_bytes : ltac2:(zQ "50!ja!hk2!h8!j6!ml1>2sx$0>1n$2>2bs@1$1$3$4") := ltac2:(zQ "a0!ja!j6!hk2!h8!md!nkc!rg6!oc!p2!s7\2sx$0\1n$3\2bs@1$2$1@1$5=1u$1@1$6^1M0\2sx$0$1^4@2$9@2$7@1$4#8@1$8^3^1^1").

(* [comment removed for export] *)
Fixpoint log_byte_lit (log : list sentry) (rb : expr) (rk : Z) : option Z :=
  match log with
  | [] => None
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk 1 kb kk (Z.of_nat w) with
      | RInside d => match v with
                     | ELit z => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
                     | _ => None
                     end
      | RDisjoint => log_byte_lit rest rb rk
      | _ => None
      end
  end.

(* [comment removed for export] *)
Fixpoint log_bytes_lit (log : list sentry) (rb : expr) (rk : Z) (n : nat) : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match log_byte_lit log rb rk, log_bytes_lit log rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint log_lookup (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) (sx : bool)
         (hints : list bool) (acc : list sidecond) : lres :=
  match log with
  | [] => LMiss acc hints
  | SE (SA kb kk) w v :: rest =>
      match rel_lit rb rk (Z.of_nat n) kb kk (Z.of_nat w) with
      | RInside d => LHit (mkExt sx (Z.to_nat d) n v) acc hints
      | RDisjoint => log_lookup kn rest rb rk n sx hints acc
      | RPartial => match log_bytes_lit log rb rk n with
                    | Some bs => LHit (lit_of_bytes sx n bs) acc hints
                    | None => LStuck
                    end
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

(* [comment removed for export] *)
Definition fill_lit : ltac2:(zQ "40!ja!h8!j6!ml1>2sx$0>1n$1>1c$2$3") := ltac2:(zQ "60!j6!ja!h8!rh8!ri2!q1\2sx$1\1n$2\1c$0@3$4^3^2@3$3$0@2$5^1+hg0^2").

(* [comment removed for export] *)
Fixpoint know_byte_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) : option Z :=
  match kn with
  | [] => None
  | K :: rest =>
      match K with
      | KWord (SA kb kk) w (ELit z) =>
          match rel_lit rb rk 1 kb kk (Z.of_nat w) with
          | RInside d => Some (((z mod two64) / 2 ^ (8 * d)) mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KZero (SA kb kk) (ELit l0) =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some 0%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KFill (SA kb kk) (ELit l0) c =>
          match rel_lit rb rk 1 kb kk (l0 mod 2 ^ 64)%Z with
          | RInside _ => Some (c mod 256)%Z
          | _ => know_byte_lit segs rest rb rk
          end
      | KImg lo hi =>
          match rb with
          | ELit 0 =>
              if (Z.leb lo rk && Z.ltb rk hi)%bool then
                match seg_rom segs (Z_to_bv 64 rk) with
                | Some b => Some (bv_unsigned b)
                | None => None            (* [comment removed for export] *)
                end
              else know_byte_lit segs rest rb rk
          | _ => know_byte_lit segs rest rb rk
          end
      | _ => know_byte_lit segs rest rb rk
      end
  end.

(* [comment removed for export] *)
Fixpoint know_bytes_lit (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z) (n : nat)
  : option (list Z) :=
  match n with
  | O => Some []
  | S n' => match know_byte_lit segs kn rb rk, know_bytes_lit segs kn rb (rk + 1) n' with
            | Some b, Some r => Some (b :: r)
            | _, _ => None
            end
  end.

(* [comment removed for export] *)
Fixpoint know_lookupA0 (allkn : list kentry) (segs : list Segment) (kn : list kentry) (rb : expr) (rk : Z)
         (n : nat) (sx : bool) (hints : list bool) (acc : list sidecond) : lres :=
  let know_lookup := know_lookupA0 allkn in
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
                  (* [comment removed for export] *)
                  if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
                  match hints with
                  | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit (ELit 0) acc hints else
              match hints with
              | true :: hs => LHit (ELit 0) (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KFill (SA kb kk) len c =>
          (* [comment removed for export] *)
          let hit := fill_lit sx n c in
          match len with
          | ELit l0 =>
              match rel_lit rb rk (Z.of_nat n) kb kk (l0 mod 2^64)%Z with
              | RInside _ => LHit hit acc hints
              | RDisjoint | RPartial => know_lookup segs rest rb rk n sx hints acc
              | RUnknown =>
                  if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
                  match hints with
                  | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
                  | false :: hs => know_lookup segs rest rb rk n sx hs acc
                  | [] => know_lookup segs rest rb rk n sx [] acc
                  end
              end
          | _ =>
              if xinside allkn rb rk (elen n) kb kk len then LHit hit acc hints else
              match hints with
              | true :: hs => LHit hit (SCInside (SA rb rk) (elen n) (SA kb kk) len :: acc) hs
              | false :: hs => know_lookup segs rest rb rk n sx hs acc
              | [] => know_lookup segs rest rb rk n sx [] acc
              end
          end
      | KUnk _ _ => know_lookup segs rest rb rk n sx hints acc   (* [comment removed for export] *)
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
                  (* [comment removed for export] *)
                  if match erange allkn len with   (* [comment removed for export] *)
                     | Some (lo, _) => Z.leb (rk + Z.of_nat n) (kk + lo)
                     | None => false
                     end
                  then LHit (EBlob sx k (rk - kk) n) acc hints
                  else
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
Definition know_lookupA : ltac2:(zQ "90!hk2!ja!np9!h8!j6!rm7!rn2!ml1!rna>5allkn@1$0$2>4segs@1$0$5>2kn@1$0$2>2rb$7>2rk$4>1n$3>2sx$1>5hints@1$0$1>3acc@1$0$8$6") := ltac2:(zQ "h00!hk2!ja!rn2!j6!rna!iob!ro6!ml1!np9!h8!rm7!roe!rp7!rq1!rr3!ri2\5allkn@1$0$8\4segs@1$0$a\2kn@1$0$8\2rb$7\2rk$3\1n$9\2sx$1\5hints@1$0$1\3acc@1$0$4M2\1x$2$2@9$e^9^8^7^6^5^4^3^2^1\1v$7\3scs@1$0$4\6hints0@1$0$1@3$6^3^2^1\4acc'@1$0$4\6hints'@1$0$1M5\1x@1$5@1$0$3$2@5$d^a^9^8^7^6\2bs@1$0$3@3$6@3$f^6^7^1^3^2@2$b^2^1$c").

Definition know_lookup : ltac2:(zQ "90!hk2!ja!h8!j6!rm7!rn2!ml1!np9!rna>4segs@1$0$4>2kn@1$0$7>2rb$6>2rk$3>1n$2>2sx$1>5hints@1$0$1>3acc@1$0$8$5") := ltac2:(zQ "90!hk2!ja!h8!j6!rm7!rs4!ml1!np9!rna\4segs@1$0$4\2kn@1$0$7\2rb$6\2rk$3\1n$2\2sx$1\5hints@1$0$1\3acc@1$0$8@9$5^7^8^7^6^5^4^3^2^1").

(* [comment removed for export] *)
Fixpoint coeffs_divk (kn : list kentry) (m : Z) (ts : list (Z * expr)) : bool :=
  match ts with
  | [] => true
  | (k, a) :: rest => ((Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0) && coeffs_divk kn m rest)%bool
  end.

Definition lin_lowbits_kn : ltac2:(zQ "50!j6!hk2!iob!ml1!np9>2kn@1$1$4>1e$3>1k$0@1$2$0") := ltac2:(zQ "h00!j6!hk2!ml1!m7!ja!js9!iq0!ju1!iob!ju6!rt4!np9!np2!ol9!ru3!q1\2kn@1$1$b\1e$2\1k$0=1l$c@1$d^2M4\0$4@1$8$0@3$a^4@2$3+2^2@3$9$0@1$1@2$5$0$2^1@2$6$0@2$f@3$7$0@1$1@2$5$0$2^1@2$3+2^2@2$e^3@2$3+2^2").   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint ldiv_terms (m : Z) (ts : list (Z * expr)) : list (Z * expr) :=
  match ts with
  | [] => []
  | (k, a) :: rest => ((k / m)%Z, a) :: ldiv_terms m rest
  end.

(* [comment removed for export] *)
Fixpoint lsplit_divc (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_divc m rest in
      if Z.eqb (k mod m) 0 then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition lin_nowrap_l : ltac2:(zQ "60!hk2!j6!ja!js9!ml1!np9>2kn@1$0$5>1c$1>2ts@1$0@2$3$1$4$2") := ltac2:(zQ "e0!j6!js9!ja!hk2!iob!jk3!hv5!rv1!ml1!np9!ot6!nl4!isa!iv4\2kn@1$3$9\1c$0\2ts@1$3@2$1$0$8M4\1x@1$4@2$1$0$0$2@3$a@1$7^3^2^1\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0@2$5@2$cZ^2@2$d^1$b$6").

Definition mkSrl : ltac2:(zQ "40!ml1!hk2!j6!np9>2kn@1$1$3>1a$0>1s$2$0") := ltac2:(zQ "he1!j6!js9!ml1!hk2!ja!jub!rvb!nkc!qh5!pb!jk3!ju1!iob!ju6!sg6!qj6!poa!sgf!shd!sib!ipa!sja!ska!sl9!rv1!np9!np2!ol9!kje!m7&@2$1@1$3@2$1$0$2@1$3@2$1$0$2\2kn@1$3$h9\1a$2\1s$0=1l$ha@1$hb^2=1m$0@2$hd+2^2M4\0$4$2@2$a@2$a@1$f@1$h3^2@2$h7^1@3$d$0@1$3@2$1$0$2^2@2$h2^5^4@1$e@4$5$0@1$3@2$1$0$2@2$9@3$b$0@1$3@2$1$0$2^2^1@2$h1^1@3$d$0@1$3@2$1$0$2^2M1\1x~0$2M4\0$4~0@2$a@1$f@1$h3^2@2$h2^5^4@2$h6^1@3$d$0@1$3@2$1$0$2^2@4$5@1$3@2$1$0$2@1$3@2$1$0$2@1$h0@2$1$0$2@1$h0@2$1$0$2\3dts@1$3@2$1$0$2\3rts@1$3@2$1$0$2M3\3dts@1$3@2$1$0$2$2^2@3$8$6^6@1$7^5\1p@2$1$0$2\2l0@1$3@2$1$0$2M3\3rts@1$3@2$1$0$2$2^3@3$8$6^8@1$7^7\2p0@2$1$0$2\2l1@1$3@2$1$0$2Mc\1x@1$c@2$1$0$0$2M4\0$4@1$c@2$1$0$0@3$h5^b@3$b$0@1$3@2$1$0$2^8^5@2$h8^b@1$e@4$5$0@1$3@2$1$0$2@3$b$0@1$3@2$1$0$2^8^5@1$h4@2$1$0$0\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0M4\0$4$2@2$hc@2$9^2^a@2$9^1^a@1$e@4$5$0@1$3@2$1$0$2@2$9^2^a@2$h1^a^9@3$8$6^d@1$7^c@3$8$6^a@1$7^9").

(* [comment removed for export] *)
Fixpoint lowbits (kn : list kentry) (e : expr) (j : Z) {struct e} : option Z :=
  let m := (2 ^ j)%Z in
  let dflt := if Z.leb j (ealign kn e) then Some 0%Z else lin_lowbits_kn kn e j in
  match e with
  | ELit z => Some ((z mod two64) mod m)%Z
  | EAlu ALU_AND a (ELit c) =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some (Z.land v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_OR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_XOR a (ELit c) =>
      match lowbits kn a j with Some v => Some (Z.lxor v ((c mod two64) mod m)) | None => dflt end
  | EAlu ALU_ADD a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x + y) mod m)%Z | _, _ => dflt end
  | EAlu ALU_SUB a b =>
      match lowbits kn a j, lowbits kn b j with Some x, Some y => Some ((x - y) mod m)%Z | _, _ => dflt end
  | EMd M_MUL (ELit c) a =>
      if Z.eqb ((c mod two64) mod m) 0 then Some 0%Z else
      match lowbits kn a j with Some v => Some ((c * v) mod m)%Z | None => dflt end
  | _ => dflt
  end.

(* [comment removed for export] *)
Fixpoint lsplit_div (kn : list kentry) (m : Z) (ts : list (Z * expr)) : list (Z * expr) * list (Z * expr) :=
  match ts with
  | [] => ([], [])
  | (k, a) :: rest =>
      let (d, r) := lsplit_div kn m rest in
      if (Z.eqb (k mod m) 0 || Z.eqb ((k * 2 ^ ealign kn a) mod m) 0)%bool then ((k, a) :: d, r) else (d, (k, a) :: r)
  end.

(* [comment removed for export] *)
Definition and_high_split : ltac2:(zQ "50!j6!ml1!hk2!js9!np9>2kn@1$2$4>2bk$1>1j$0>1c$0>3dts@1$2@2$3$0$1>3rts@1$2@2$3$0$1$1") := ltac2:(zQ "h40!j6!ml1!js9!hk2!jub!qh5!sg6!pb!ja!iob!kkd!om3!q1!rv1!np9!jk9!kje!l8!m7!iqe\2kn@1$3$e\2bk$1\1j$0\1c$0\3dts@1$3@2$2$0$1\3rts@1$3@2$2$0$1=1m$0@2$h2+2^4=2cA$0@2$h3^4@2$c^4^1=1r$1@1$6@4$4$0@1$3@2$2$0$1@2$c^5^2^3M9\1x@1$9@2$2$0$0$1@2$d^9^1\1p@2$2$0$0M2\1p@2$2$0$0$1^1\2lo$0\2hi$0M8\0$8$1@2$h0@2$7^2^6@2$7^1^6@1$6@4$4$0@1$3@2$2$0$1@2$f^5@2$h1@2$7^2^6^6^8@3$5$a@1$6@4$4$0@1$3@2$2$0$1^5^8@3$5$b^4^b@3$5$a@1$6@4$4$0@1$3@2$2$0$1^2^5@3$5$b^1^8").

Definition and_low_split : ltac2:(zQ "50!j6!ml1!hk2!js9!np9>2kn@1$2$4>2bk$1>1j$0>1c$0>3rts@1$2@2$3$0$1$1") := ltac2:(zQ "h20!j6!ml1!js9!hk2!pb!ja!iob!jub!om3!qh5!sg6!q1!rv1!np9!kje!l8!m7!iqe\2kn@1$3$d\2bk$1\1j$0\1c$0\3rts@1$3@2$2$0$1=1m$0@2$h0+2^3=1r$1@1$a@4$7$0@1$3@2$2$0$1@2$b^3^1^2M6\1x@1$6@2$2$0$0$1@2$c^7^1\1p@2$2$0$0M2\1p@2$2$0$0$1^1\2lo$0\2hi$0M5\0$5$1@2$e@2$4^2^5@2$4^1^5@1$a@4$7$0@1$3@2$2$0$1@2$h1@2$b^7^5@2$f@2$4^2^5^5^6@3$9$8^4^9@3$9$8^1^6").

(* [comment removed for export] *)
Definition mkAnd0 : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1a$0>1b$0$0") := ltac2:(zQ "ib4!ml1!j6!js9!hk2!ja!om3!qh5!m7!iob!nkc!jk3!h8!ju6!ol9!ju1!sib!nl4!jk9!isa!ou3!iv4!iqe!qj6!jub!ki8!huc!ig2!sm7!sn9!so7!sp0!spa!kje!q1!poa!sq2!sr4!rt4!ss5!np9!np2!sg6!iud&@2$2@1$3@2$2$1$0@1$3@2$2$1$0&\1x~0$0&\2op$h9\2a0$0\2b0$0@3$6$5^5^4&\2op$ha\2a0$0\2b0$0@3$6$5^5^4\2kn@1$3$i7\1a$0\1b$0M0\1b$0$0^1\1k$1=2k'$1@2$i1^1$h0=1j$1@1$h3@2$h5$h0^1M4\0$4$0@2$a@2$i0@2$h5$h0^2@2$7+2^1@2$h4^1+k0M4\0$4$0@2$h2^1@2$he^6^5^5=1l$i8@1$d^5M4\0$4$0@2$a@1$h6@1$f^1@3$i5^7@2$7+2^2@3$c$1@1$3@2$2$1$0^1@1$i9@4$h7$1@1$3@2$2$1$0@2$h5@3$e$1@1$3@2$2$1$0^1@2$i1@3$e$1@1$3@2$2$1$0^1@2$7+2^2@3$c$1@1$3@2$2$1$0^1M2~1M4\0$4~0@1$f^1@4$h7@1$3@2$2$1$0@1$3@2$2$1$0@1$i2@2$2$1$0@3$c$1@1$3@2$2$1$0^1@3$hc^7@2$7+2^2@3$c$1@1$3@2$2$1$0^1\3dts@1$3@2$2$1$0\3rts@1$3@2$2$1$0M3\3dts@1$3@2$2$1$0$0^2@3$hf$h8@1$9@2$7+2^4@3$hd^9^8^4\1p@2$2$1$0\2l0@1$3@2$2$1$0M3\3rts@1$3@2$2$1$0$0^3@3$hf$h8@1$9@2$7+2^6@3$hd^b^a^6\2p0@2$2$1$0\2l1@1$3@2$2$1$0@6$i3^d^b^8@3$e$1@1$3@2$2$1$0^7^6^5=2j2$1@1$h3@2$h1^2+1M4\0$4$0@2$a@2$i0@2$h1^3+1@2$7+2^1@2$h4^1+k0M4\0$4$0@2$h2^1@2$he^7^6@1$9ZM8\1x@1$8$1$0@3$i6^7^6^1\1v$1@1$9^1M4\0$4$0@1$f@1$d^6@3$6$5^6^5M8\1x@1$8$1$0@3$hb^7^6^1\1v$1@1$9^1M2~1@3$hc^7@2$7+2^1@3$c$1@1$3@2$2$1$0@1$d^6\1l@1$3@2$2$1$0\3rts@1$3@2$2$1$0M3\1l@1$3@2$2$1$0$0^2@3$6$5^8^7\1p@2$2$1$0\2l0@1$3@2$2$1$0M3\3rts@1$3@2$2$1$0$0^3@3$6$5^a^9\2p0@2$2$1$0\2l1@1$3@2$2$1$0@5$i4^d^b^7@3$e$1@1$3@2$2$1$0@1$d^c^5=2j3$1@2$h1@1$h3^3+1M4\0$4$0@2$a@2$a@2$h4Z^4@2$h2^1+k0@1$h6@1$f@1$d^7M8\1x@1$8$1$0@3$hb^8^7^1\1v$1@1$9@2$ia^1^5@3$6$5^7^6@3$6$5^7^6\1n$b@3$6$5^3^2~2~2~3~3\2sx$4\2lo$b\1n$b\1e$0@3$6$5^6^5\2sx$4\1k$b\1i$1\1n$b@3$6$5^6^5").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition narrow_mask : ltac2:(zQ "50!j6!hk2!iob!ml1!np9>2kn@1$1$4>1a$3>2k'$0@1$2$0") := ltac2:(zQ "h20!j6!iob!ja!m7!ipa!iv4!jk3!iq0!hk2!st0!ml1!np9!nl4!st9!jk9!kje!ou3!iqe\2kn@1$8$b\1a$a\2k'$0=1i$0@1$9^1=1m$0@2$e^2@2$3+2^1=1j$0@1$h0^1M2\0$2@1$1$0@2$6@2$6@2$5Z^4@2$f^2@2$3+2^1@2$5^1+k0M1\1x@1$1$0@1$1$0@2$d^6^5\1h$0M2\0$2@1$1$0@2$5^1@2$3+2^2@2$7$0@2$h1$c@2$3+2^4@1$4$0@1$4$0@1$4$0").

Definition mkAnd : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1a$0>1b$0$0") := ltac2:(zQ "e2!ml1!su0!h8!j6!ja!iob!huc!ig2!hk2!nkc!sua!np9!nl4!q1&\2op$6\2a0$0\2b0$0@3$1^6^5^4&\2op$7\2a0$0\2b0$0@3$1^6^5^4\2kn@1$8$b\1a$0\1b$0M0\1b$0$0^1\1k$3M5\1x@1$5$3$0@3$a^4^3@2$d^1$c\1m$3@3$1^5^4@1$9^1@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1\2sx$4\2lo$2\1n$2\1e$0@3$1^7^6^5\2sx$4\1k$2\1i$3\1n$2@3$1^7^6^5").

Definition mkAndK : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1a$0>1b$0$0") := ltac2:(zQ "h0h3!ml1!sv9!h8!huc!ja!ig2!j6!nl4!q1!nkc!iud!m7!hk2!np9!kje!iqe&\3op0$3\2a0$0\2b1$0@3$1^a^9^8&\3op0$5\2a0$0\2b1$0@3$1^a^9^8&\2lo$2\1n$2\1e$0@3$1^b^a^9&\2sx$4~2&\1k$2\1i$6\1n$2@3$1^b^a^9&\2sx$4~4&\3op0$3\2a0$0\2b1$0@3$1^9^8^7&\3op0$5\2a0$0\2b1$0@3$1^9^8^7&\2lo$2\1n$2\1e$0@3$1^a^9^8&\2sx$4~8&\1k$2\1i$6\1n$2@3$1^a^9^8&\2sx$4~a&\3op1$3\2a1$0\2b2$0@3$1^e^d^c&\3op1$5\2a1$0\2b2$0@3$1^e^d^c&\3op1$3\2a1$0\2b2$0@3$1^d^c^b&\3op1$5\2a1$0\2b2$0@3$1^d^c^b&\3op0$5\2a1$0\2b1$0@3$1^a^9^8&\3op0$3\2a1$0\2b1$0@3$1^9^8^7&\3op0$5\2a1$0\2b1$0@3$1^9^8^7\2kn@1$c$d\1a$0\1b$0M0\1a$0$0^2\1z$6@3$1^4^3^2\1n$2@3$1^4^3^2\2op$3\1x$0\2b0$0M3\2op$3$0^3@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4M0\2b0$0$0^1\2m1$6M0\1b$0$0^5\1k$6@3$1^8^4@1$9@2$a@2$8^2$7@2$8^1$7\1n$2@3$1^8^7^6~0~0~1~1~3~5\1n$2@3$1^7^6^5~6~6~7~7~9~b\2op$3\2a0$0\2b0$0@3$1^6^5^4\2op$5\2a0$0\2b0$0M5\2op$5$0^3M0\2a0$0$0^2\1m$6M0\2b0$0$0^2\1z$6@3$1^8^7^6\1n$2@3$1^8^7^6\3op0$3\1x$0\2b1$0M3\3op0$3$0^3@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8M0\2b1$0$0^1\1i$6M0\1b$0$0^9\1k$6=2i'$6@2$8@2$8^2$7+k0M4\0$4$0@2$e@2$8^7$7@2$b+2^1@3$1^d^5@1$9@2$a@2$f$7@2$b+2^1@2$8^2$7@3$1^d^c^b\1n$2@3$1^c^b^a~c~c~d~d\2sx$4\2lo$2\1n$2\1e$0@3$1^f^e^d\2sx$4\1k$2\2i0$6\1n$2@3$1^f^e^d\1n$2@3$1^b^a^9~e~e~f~f\2sx$4\2lo$2\1n$2\1e$0@3$1^e^d^c\2sx$4\1k$2\1i$6\1n$2@3$1^e^d^c@3$1^a^9^8@3$1^a^9^8@3$1^a^9^8\3op0$3\2a1$0\2b1$0@3$1^a^9^8~h0~h0~3~5\1n$2@3$1^7^6^5~h1~h1~h2~h2~9~b@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4@3$1^6^5^4\2op$5\2a0$0\2b0$0@3$1^6^5^4\2sx$4\2lo$2\1n$2\1e$0@3$1^7^6^5\2sx$4\1k$2\1i$6\1n$2@3$1^7^6^5").

(* [comment removed for export] *)
Definition or_disjoint : ltac2:(zQ "40!ml1!ja!hk2!np9>2kn@1$2$3>1a$0>1b$0$1") := ltac2:(zQ "e0!j6!js9!ja!iob!ml1!jk3!hv5!hk2!sp0!rv1!np9!isa!iv4!m7\2kn@1$7$a\1a$4\1b$4M3\1x@1$3@2$1$0$0$2@2$9^3^1\1p@2$1$0$0M1\1p@2$1$0$0$2^1\2lo$0\2hi$0@2$5@2$bZ^2@2$c^1@2$d+2@2$8^6^5$6").

Definition mkOr : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1a$0>1b$0$0") := ltac2:(zQ "h5ia!ml1!tg2!ome!h8!ja!j6!nkc!huc!ig2!kkd!qh5!tgc!nl4!th6!q1!iob!thd!tic!hk2!np9!tj6&\2op$7\2a0$0\2b0$0@3$2$1^7^6&\2op$8\2a0$0\2b0$0@3$2$1^7^6&@3$b^8^6@1$6@1$d@2$e^1$c&@3$a$9~2@1$6^1&\1c$5~3&\2op$7\2a0$0\2b0$0@3$2$1^9^8&\2op$8\2a0$0\2b0$0@3$2$1^9^8&\2lo$3\1n$3\1e$0@3$2$1^a^9&\2sx$4~7&\1k$3\1i$5\1n$3@3$2$1^a^9&\2sx$4~9&M0\1a$0$0^6~4\1n$3@3$2$1^7^6~5~5~6~6~8~a&\2b0$0~b&\2a0$0~c&\2op$7~d&\2op$8~d&@3$b^9^7@1$6@1$d@2$e^1$c&@3$a$9~h0@1$6^1&\1c$5~h1&\2op$7\2a0$0\2b0$0@3$2$1^a^9&\2op$8\2a0$0\2b0$0@3$2$1^a^9&\2lo$3\1n$3\1e$0@3$2$1^b^a&\2sx$4~h5&\1k$3\1i$5\1n$3@3$2$1^b^a&\2sx$4~h7&M0\1a$0$0^7~h2\1n$3@3$2$1^8^7~h3~h3~h4~h4~h6~h8&\2op$7\2a0$0\2b0$0@3$2$1^6^5&\2op$8\2a0$0\2b0$0@3$2$1^6^5&@3$b^7^5@1$6@1$d@2$e^1$c&@3$a$9~hc@1$6^1&\1c$5~hd&\2op$7\2a0$0\2b0$0@3$2$1^8^7&\2op$8\2a0$0\2b0$0@3$2$1^8^7&\2lo$3\1n$3\1e$0@3$2$1^9^8&\2sx$4~i1&\1k$3\1i$5\1n$3@3$2$1^9^8&\2sx$4~i3&M0\1a$0$0^5~he\1n$3@3$2$1^6^5~hf~hf~i0~i0~i2~i4&\2b0$0~i5&\2a0$0~i6&\2op$7~i7&\2op$8~i7\2kn@1$h2$h3\1a$0\1b$0Mf\1x@1$f$5$0@1$h1^2\1x$5Mf\1x@1$f$5$0@1$h1^2\1y$5@1$6@3$h4$1^2^1M4\0$4$0@3$h0^4^3^2@3$a$9^3^2M4\0$4$0@3$h0^4^2^3@3$a$9^3^2M0\1b$0$0^2\1c$5@3$a$9@3$b^5^4@1$6@1$d@2$e^1$c@1$6^1\1n$3M0\1a$0$0^4\1c$5@3$a$9@3$b^6^4@1$6@1$d@2$e^1$c@1$6^1\1n$3@3$2$1^5^4~0~0~1~1\2sx$4\2lo$3\1n$3\1e$0@3$2$1^8^7\2sx$4\1k$3\1i$5\1n$3@3$2$1^8^7~e~e~f~f\2sx$4\2lo$3\1n$3\1e$0~h9\2sx$4\1k$3\1i$5\1n$3~h9M4\0$4$0@3$h0^3^2^1@3$a$9^2^1M4\0$4$0@3$h0^3^1^2@3$a$9^2^1M0\1b$0$0^1\1c$5@3$a$9@3$b^4^3@1$6@1$d@2$e^1$c@1$6^1\1n$3M0\1a$0$0^3\1c$5@3$a$9@3$b^5^3@1$6@1$d@2$e^1$c@1$6^1\1n$3@3$2$1^4^3~ha~ha~hb~hb\2sx$4\2lo$3\1n$3\1e$0@3$2$1^7^6\2sx$4\1k$3\1i$5\1n$3@3$2$1^7^6~i8~i8~i9~i9\2sx$4\2lo$3\1n$3\1e$0~b\2sx$4\1k$3\1i$5\1n$3~b").

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
           | Some w => if Z.eqb w v then all_eval_to s e v (lo + 1) c else false   (* [comment removed for export] *)
           | None => false
           end
  end.

Fixpoint evalS (s : expr) (z : Z) (e : expr) : option Z :=
  if expr_eqb e s then Some z else
  match e with
  | ELit w => Some (wrap64 w)
  | EVar _ => None
  | EAlu op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zfast op x y) | None => None end
                   | None => None
                   end
  | EAluw op a b => match evalS s z a with
                    | Some x => match evalS s z b with Some y => Some (zfastw op x y) | None => None end
                    | None => None
                    end
  | EMd op a b => match evalS s z a with
                  | Some x => match evalS s z b with Some y => Some (zfastm op x y) | None => None end
                  | None => None
                  end
  | EMdw op a b => match evalS s z a with
                   | Some x => match evalS s z b with Some y => Some (zmdw op x y) | None => None end
                   | None => None
                   end
  | EExt sx lo n a => match evalS s z a with
                      | Some x => Some (zext_fast sx lo n x) | None => None end   (* [comment removed for export] *)
  | EBlob _ _ _ _ => None
  end.

(* [comment removed for export] *)
Fixpoint all_eval_toS (s e : expr) (v lo : Z) (cnt : nat) : bool :=
  match cnt with
  | O => true
  | S c => match evalS s (wrap64 lo) e with
           | Some w => if Z.eqb w v then all_eval_toS s e v (lo + 1) c else false
           | None => false
           end
  end.

(* [comment removed for export] *)
Definition probeS : ltac2:(zQ "30!j6!ml1!ja>1s$1>1e$1>1v$0>1z$0$2") := ltac2:(zQ "80!j6!iob!ml1!ja!hv5!tje!tk7!kje\1s$2\1e$2\1v$0\1z$0M1\1x@1$1$0$3@3$5^4@1$6^1^3\1w$0@2$7^1^3$4").

Fixpoint memE (e : expr) (l : list expr) : bool :=
  match l with [] => false | x :: r => if expr_eqb e x then true else memE e r end.

Fixpoint nubE_acc (l acc : list expr) : list expr :=
  match l with
  | [] => []
  | x :: r => if memE x acc then nubE_acc r acc else x :: nubE_acc r (x :: acc)
  end.
Definition nubE : ltac2:(zQ "20!hk2!ml1>1l@1$0$1@1$0$1") := ltac2:(zQ "40!ml1!hk2!poa!tl1\1l@1$1$0@2$3^1@1$2$0").

Definition conc_limit : Z := 4096.

(* [comment removed for export] *)
Fixpoint evalS_def (s e : expr) : bool :=
  if expr_eqb e s then true else
  match e with
  | ELit _ => true
  | EVar _ => false
  | EAlu _ a b | EAluw _ a b | EMd _ a b | EMdw _ a b => if evalS_def s a then evalS_def s b else false
  | EExt _ _ _ a => evalS_def s a
  | EBlob _ _ _ _ => false
  end.

Fixpoint conc_try (kn : list kentry) (e : expr) (cands : list expr) : option Z :=
  match cands with
  | [] => None
  | s :: rest =>
      if closedb s then conc_try kn e rest else
      if negb (evalS_def s e) then conc_try kn e rest else
      match erange kn s with
      | Some (lo, hi) =>
          if Z.leb (hi - lo) conc_limit then
            match evalS s (wrap64 lo) e with
            | Some v =>
                if (if Z.ltb hi lo then true
                     else if probeS s e v hi then probeS s e v (lo + (hi - lo) / 2)%Z else false) then
                  if all_eval_toS s e v lo (Z.to_nat (hi - lo + 1)) then Some v
                  else conc_try kn e rest
                else conc_try kn e rest
            | None => conc_try kn e rest
            end
          else conc_try kn e rest
      | None => conc_try kn e rest
      end
  end.

(* [comment removed for export] *)


Definition concretize : ltac2:(zQ "50!hk2!iob!j6!ml1!np9>2kn@1$0$4>1e$3@1$1$2") := ltac2:(zQ "b0!ja!hk2!iob!j6!tld!tm8!tn4!to3!tob!ml1!np9\2kn@1$1$a\1e$9M0\0$0@1$2$3@1$4^1@1$6^1@3$5^2^1@1$7@1$8^1").

(* [comment removed for export] *)
Definition foldK : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1e$0$0") := ltac2:(zQ "eh4!j6!ml1!iob!js9!nkc!ja!tp7!rv1!kje!h8!huc!ig2!hk2!np9&M2\1x@1$2$0$1@2$6^6^5\1v$0@1$4^1^5&M2\1x@1$2$0$1@2$6^8^7\1v$0@1$4^1^7&M5\0$5$1@2$8^2^1@1$4^2~1&\2hi$0~2&\2lo$0~3&M3\1p@2$3$0$0$1^1~4&\1p@2$3$0$0~5&M2\1x@1$2$0$1@2$6^5^4\1v$0@1$4^1^4&M2\1x@1$2@2$3$0$0$1@2$7^5^4~6~7&\1b$1~8&\1a$1~9&\2op$a~a&\2op$b~a&M2\1x@1$2$0$1@2$6^9^8\1v$0@1$4^1^8&M5\0$5$1@2$8^2^1@1$4^2~d&\2hi$0~e&\2lo$0~f&M3\1p@2$3$0$0$1^1~h0&\1p@2$3$0$0~h1&M2\1x@1$2@2$3$0$0$1@2$7^6^5~h2~0\2kn@1$c$d\1e$1M1\1e$1$1^1\1z$0^2\1n$9M2\1x@1$2@2$3$0$0$1@2$7^3^2\1p@2$3$0$0M3\1p@2$3$0$0$1^1\2lo$0\2hi$0M5\0$5$1@2$8^2^1@1$4^2~0M2\1x@1$2$0$1@2$6^3^2\1v$0@1$4^1^2~b~b~c~c\2sx$5\2lo$9\1n$9\2e0$1~h3\2sx$5\1k$9\1i$0\1n$9~h3").

Definition lit_branch : ltac2:(zQ "30!j6!ja!tq5>1c$2>1x$0>1y$0$1") := ltac2:(zQ "50!md!j6!hia!tq5!tr4\1c$3\1x$1\1y$1@3$4^3@2$2@1$0#k0^2@2$2@1$0#k0^1").

(* [comment removed for export] *)
Definition cond_on_eq : ltac2:(zQ "20!ja!tq5>1c$1$0") := ltac2:(zQ "40!hv5!hvc!tq5!ja\1c$2M2\1c$2$3^1$1$0$0$1$0$1").

(* [comment removed for export] *)
Definition itv_ltu : ltac2:(zQ "30!j6!ja!iob>2al$0>2ah$0>2bl$0>2bh$0@1$2$1") := ltac2:(zQ "90!ja!j6!iq0!iob!ipa!hv5!hvc!isa!iv4\2al$1\2ah$1\2bl$1\2bh$1M0\0$0@1$3$0@2$8^3^2@2$2$0$6M0\0$0@1$3$0@2$7^1^4@2$2$0$5@1$4$0").

(* [comment removed for export] *)
Definition itv_lts : ltac2:(zQ "30!j6!ja!iob>2al$0>2ah$0>2bl$0>2bh$0@1$2$1") := ltac2:(zQ "d0!ja!j6!jk3!isa!iv4!iob!iq0!ipa!hv5!ngb!hvc!ts4!m7\2al$1\2ah$1\2bl$1\2bh$1=1h$1@2$c+2+jfM0\0$0@1$5$0@2$9@2$2@2$4^4^1@2$4^2^1@2$2@2$3^1^5@2$3^1^3@4$b^5^4^3^2M0\0$0@1$5$0@2$2@2$3^1^5@2$4^2^1@2$6$0$aM0\0$0@1$5$0@2$2@2$4^4^1@2$3^1^3@2$6$0$8@1$7$0").

Definition range_branch : ltac2:(zQ "40!j6!ja!iob!tq5>1c$3>2al$0>2ah$0>2bl$0>2bh$0@1$2$1") := ltac2:(zQ "h01!ja!kje!iob!iq0!jk3!j6!iv4!tq5!ipa!hv5!qj6!tsf!ngb!hvc!ttb!ts4&@2$4@2$4@2$1^4^3@2$1^2^1@2$1^4^2\1c$7\2al$5\2ah$5\2bl$5\2bh$5M7\1c$7@1$2$0^5M0\0$0@1$2$0@2$c@2$6^3^2@2$6^1^4@2$3$0$9M0\0$0@1$2$0~0@2$3$0$d@1$8$0M0\0$0@1$2$0@2$c@2$6^3^2@2$6^1^4@2$3$0$dM0\0$0@1$2$0~0@2$3$0$9@1$8$0@4$e^4^3^2^1@4$b$0$0$a@4$e^4^3^2^1@4$f^4^3^2^1@4$b$0$0$a@4$f^4^3^2^1").

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition diff_branch : ltac2:(zQ "40!ml1!ja!iob!tq5>1c$3>1a$0>1b$0@1$2$1") := ltac2:(zQ "e5!ja!qj6!iob!tq5!ipa!j6!iq0!tu6!ml1!tic!qh5!nl4!kje!q1&M3\1c$3$0^5^1@1$1^1@1$1^1@1$1^1@1$1^1@1$1^1&@2$6$0~0&=1e$0@2$c@2$d^1$bZ~1&\1z$5~2&M2\1x@1$2$5@1$2$0@1$9@3$a$7^2^1~3@1$4$0\1c$3\1a$8\1b$8M3\1c$3@1$2$0^3~4~4@1$4$0@1$4$0@1$4$0@1$4$0").

(* [comment removed for export] *)
Definition lin_branch : ltac2:(zQ "60!ml1!ja!hk2!iob!tq5!np9>2kn@1$2$5>1c$4>1a$0>1b$0@1$3$1") := ltac2:(zQ "h7hb!j6!ja!ml1!js9!iob!ov3!poa!jub!hv5!tq5!hvc!qj6!tsf!tv1!ipa!iq0!rv1!iv4!m7!jk3!ngb!hk2!np9&@3$5@2$3$2$0@4$7$2$0^2Z@1$6@2$3$2$0&@3$5@2$3$2$0@4$7$2$0^2-1@1$6@2$3$2$0&@3$5@2$3$2$0@4$7$2$0^3Z@1$6@2$3$2$0&@3$d^5~1~2&@3$5@2$3$2$0@4$7$2$0^3-1@1$6@2$3$2$0&@3$d^5~4~0&@2$h4~3~5&@2$f$1M9\1c$9$1^4$8$a$a$a$a$a&@3$d^5~2~0&@3$d^5~0~2&M1\0$1$1~8~9$8&@2$f$1M9\1c$9$1^4$a$8$8$8$8$8&M1\0$1@1$4$1~a~b@1$e$1&M1\0$1@1$4$1~6~7~c&@2$h3@2$h1^4@2$h2+2+jf@2$h1^1@2$h2+2+jf&M9\1c$9@1$4$1^a@4$c$1$1$b^7@4$c$1$1$b^7^7@4$c$1$1$b^7@4$c$1$1$b^7@4$c$1$1$b^7&M1\0$1@1$4$1~e~f@1$e$1&\2bh$0~h0&\2z0$0~h1&M3\2p0@2$3$0$0@1$4$1^1~h2&\2p0@2$3$0$0~h3&M4\1x@1$4@2$3$0$0@1$4$1@2$h0^8^5~h4@1$e$1&\2ah$0~h5&\1z$0~h6&M3\1p@2$3$0$0@1$4$1^1~h7&\1p@2$3$0$0~h8&M4\1x@1$4@2$3$0$0@1$4$1@2$h0^5^3~h9@1$e$1\2kn@1$h5$h6\1c$9\1a$2\1b$2=3ltu@1$4$1M1\0$1@1$4$1@3$d^4@3$5@2$3$2$0@4$7$2$0^1-1@1$6@2$3$2$0~0@2$f$1$aM1\0$1@1$4$1@3$d^4~0@3$5@2$3$2$0@4$7$2$0^1Z@1$6@2$3$2$0@2$f$1$8@1$e$1M9\1c$9@1$4$1^4~d~d~ha~ha^1@4$c$1$1$b^1").

Definition decide_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  match a, b with
  | ELit x, ELit y => Some (lit_branch c x y)
  | _, _ =>
      if expr_eqb a b then Some (cond_on_eq c)
      else match diff_branch c a b with
           | Some t => Some t
           | None =>
             match (match erange kn a, erange kn b with
                    | Some (al, ah), Some (bl, bh) => range_branch c al ah bl bh
                    | _, _ => None
                    end) with
             | Some t => Some t
             | None => lin_branch kn c a b      (* [comment removed for export] *)
             end
           end
  end.


(* [comment removed for export] *)
Definition mkSlt : ltac2:(zQ "50!ml1!hk2!huc!tq5!np9>2kn@1$1$4>1c$3>2op$2>1a$0>1b$0$0") := ltac2:(zQ "dc!ja!ml1!iob!nkc!qh5!uk5!h8!huc!j6!ig2!hk2!tq5!np9&\2b0$0M0\2b0$0$1^1@1$3+1@1$3Z&M2\1x@1$2$0$1@4$5^9^8^6^5~0@3$4^7^6^5&\2b0$1~1&\2a0$1~2&\3op0$7~3&\3op0$9~3&M2\1x@1$2$0$1@4$5^a^9^7^6~0@3$4^8^7^6&M2\1x@1$2$0$1@4$5^8^7^5^4~0@3$4^6^5^4&\2b0$1~7&\2a0$1~8&\3op0$7~9&\3op0$9~9\2kn@1$a$c\1c$b\2op$7\1a$1\1b$1M1\1a$1$1^2\1z$8M1\1b$1$1^2\2z0$8@3$4^5^4^3\1n$6M2\1x@1$2$0$1@4$5^7^6^4^3~0@3$4^5^4^3~4~4~5~5\2sx$0\2lo$6\1n$6\1e$1~6\2sx$0\1k$6\1i$8\1n$6~6\1n$6M2\1x@1$2$0$1@4$5^6^5^3^2~0@3$4^4^3^2~a~a~b~b\2sx$0\2lo$6\1n$6\1e$1~1\2sx$0\1k$6\1i$8\1n$6~1").

Definition mkAluK0 : ltac2:(zQ "40!ml1!hk2!huc!np9>2kn@1$1$3>2op$2>1a$0>1b$0$0") := ltac2:(zQ "hc6!ml1!qh5!h8!tgc!ja!j6!huc!iob!ig2!nl4!nkc!ul6!nk0!tic!iqe!hk2!ulf!uma!tu6!un6!unf!sv9!uo9!so7!np9!up1!kje!q1&\3op0$6\2a0$0\2b0$0@3$1^6^5^4&\3op0$8\2a0$0\2b0$0@3$1^6^5^4&\3op0$6\2a0$0\2b0$0@3$3^8^5^6&\3op0$8\2a0$0\2b0$0@3$3^8^5^6&\3op0$6\2a0$0\2b0$0@3$3^7^5^4&\3op0$8\2a0$0\2b0$0@3$3^7^5^4\2kn@1$f$h8\2op$6\1a$0\1b$0M6\2op$6$0^3@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1@5$b^4$h3$h0^2^1@5$b^4$h4$h1^2^1M4\0$4$0@2$c^2^1@1$aZM7\1x@1$7$5$0@1$d^2\1z$5@3$1^4^3^2M0\1b$0$0^1\1k$5M4\0$4$0@2$ha@2$hb^1$9@2$e$9+1@3$1$h2@1$a@2$e$9+1^3@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1\2sx$4\2lo$2\1n$2\1e$0@3$1^7^6^5\2sx$4\1k$2\1i$5\1n$2@3$1^7^6^5M7\1x@1$7$5$0@1$d^2\1z$5@3$1^4^3^2M7\1x@1$7$5$0@2$h9^1+6\1s$5@3$h7^5^3^1@3$1^3^2^1@3$1^3^2^1M4\0$4$0@2$c^2^1^2@3$h6^4^2^1M0\1a$0$0^2\1z$5M0\1b$0$0^2\2z0$5@3$h5^6^4^3\1n$2@3$3^6^3^4~2~2~3~3\2sx$4\2lo$2\1n$2\1e$0@3$3^9^6^7\2sx$4\1k$2\1i$5\1n$2@3$3^9^6^7\1n$2@3$3^5^3^2~4~4~5~5\2sx$4\2lo$2\1n$2\1e$0@3$3^8^6^5\2sx$4\1k$2\1i$5\1n$2@3$3^8^6^5").

(* [comment removed for export] *)
Definition zsx32 : ltac2:(zQ "10!j6>1v$0$0") := ltac2:(zQ "50!md!j6!nl4!q1!s7\1v$1@2$3@2$4@1$0#i0^1$2").

Definition mkAluK : ltac2:(zQ "40!ml1!hk2!huc!np9>2kn@1$1$3>2op$2>1a$0>1b$0$0") := ltac2:(zQ "60!ml1!hk2!huc!upd!uq6!np9\2kn@1$1$5\2op$2\1a$0\1b$0@2$3^4@4$4^4^3^2^1").

(* [comment removed for export] *)
Definition pow2_log : ltac2:(zQ "20!j6!iob>1m$0@1$1$0") := ltac2:(zQ "c0!j6!jk3!ja!iv4!ipa!iq0!iob!nl4!kje!ou3!q1!m7\1m$0=2m'$0@2$a^1$7=1k$0@1$9^1M2\0$2@1$6$0@2$1@2$1@2$3Z^2@2$8^2@2$b+2^1@2$3^1+k0@2$5$0^1@1$4$0").

Definition mkMdK : ltac2:(zQ "40!ml1!hk2!ig2!np9>2kn@1$1$3>2op$2>1a$0>1b$0$0") := ltac2:(zQ "h26!ml1!spa!h8!j6!ig2!iob!ja!huc!nkc!ur1!urb!hk2!om3!rvb!tic!np9!m7!iqe&\3op0$7\2a0$0\2b0$0@3$1^6^5^4&\3op0$4\2a0$0\2b0$0@3$1^6^5^4&\2lo$2\1n$2\1e$0@3$1^7^6^5&\2sx$6~2&\1k$2\1i$3\1n$2@3$1^7^6^5&\2sx$6~4\2kn@1$b$f\2op$4\1a$0\1b$0M5\1x@1$5$3$0@1$e^2\1z$3@3$1^4^3^2M4\2op$4$0^3@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1@3$1^3^2^1M0\1b$0$0^1\1m$3M5\1x@1$5$3$0@1$a^1\1k$3@4$9^6$d^4@1$8^1@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1~3~5@3$1^3^2^1M0\1b$0$0^1\1m$3M5\1x@1$5$3$0@1$a^1\1k$3@4$9^6$c^4@1$8@2$h1@2$h0+2^1+1@3$1^4^3^2\1n$2@3$1^4^3^2~0~0~1~1~3~5").

(* [comment removed for export] *)
Definition sx32_stable : ltac2:(zQ "20!j6!ja>2lo$0>2hi$0$1") := ltac2:(zQ "70!j6!m7!ngb!nl4!isa!iv4!iqe\2lo$0\2hi$0@2$2@2$5^1@2$1+2+hf@2$4@2$6$3@2$1+2+hf^2").

(* [comment removed for export] *)
Definition zband32 : ltac2:(zQ "40!ja!hk2!ml1!np9>2kn@1$1$3>1d$2$0") := ltac2:(zQ "h20!j6!js9!hk2!ml1!ja!iob!iv4!m7!jk3!hv5!ju1!ju6!rv1!np9!np2!ol9!ot6!ir4\2kn@1$2$d\1d$3=1l$e@1$f^1M5\1x@1$5@2$1$0$0$4@3$h0@1$c^3@3$a$0@1$2@2$1$0$3^1@3$b$0@1$2@2$1$0$3^1\1p@2$1$0$0M1\1p@2$1$0$0$4^1\2lo$0\2hi$0@2$8@2$6@1$h1@2$7+2+hf^2@2$6^1@2$7+2+hf$9").

Definition mkAluwK0 : ltac2:(zQ "40!ml1!hk2!huc!np9>2kn@1$1$3>2op$2>1a$0>1b$0$0") := ltac2:(zQ "h0a!j6!ml1!ja!us7!iob!js9!ut1!huc!nkc!utc!uub!rv1!tic!qh5!hk2!np9&M2\0$2$1@2$6^8^4^4@3$3^7^6^5&M2\0$2$1@2$9^2^1^4~0&\2hi$0~1&\2lo$0~2&M5\1p@2$5$0$0$1^1~3&\1p@2$5$0$0~4&M2\0$2$1@2$6^5^1^1@3$3^4^3^2&M4\1x@1$4@2$5$0$0$1@2$b^5^1~5~6&M4\1x@1$4$0$1@1$c^1\1v$0@1$8@1$a^1~7&=1d$1@3$d^3^2^1~8\2kn@1$e$f\2op$7\1a$1\1b$1M7\2op$7$1^3~9~9@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1@3$3^3^2^1").

Definition mkAluwK : ltac2:(zQ "40!ml1!hk2!huc!np9>2kn@1$1$3>2op$2>1a$0>1b$0$0") := ltac2:(zQ "60!ml1!hk2!huc!upd!uv4!np9\2kn@1$1$5\2op$2\1a$0\1b$0@2$3^4@4$4^4^3^2^1").

(* [comment removed for export] *)
Definition extK0 : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1v$0$0") := ltac2:(zQ "h10!ml1!j6!ja!h8!js9!iob!huc!ig2!l8!le!m7!hk2!rv1!np9!lj6!pb!iv4\2kn@1$b$d\1v$0M0\1v$0$0^1\1z$1^2\1n$3^2\2op$6\1a$0\1b$0^4\2op$6\1a$0\1b$0^4\2op$7\1a$0\1b$0^4\2op$7\1a$0\1b$0^4\2sx$2\2lo$3\1n$3\1e$0M3\2lo$3$0^3M2\0$2$0@2$e^2N7M5\1x@1$5@2$4$1$1$0@2$c^6^1\1p@2$4$1$1M4\1p@2$4$1$1$0^1\2lo$1\2hi$1M2\0$2$0@2$h0^1M2\2sx$2$1^7@2$f@2$a+2@2$8+8@1$9^5+2@2$a+2@2$8+8@1$9^5^4^8^5^5\2n0$3^6\2sx$2\1k$3\1i$1\1n$3^5").

Definition extK : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1v$0$0") := ltac2:(zQ "50!hk2!vg0!upd!ml1!np9\2kn@1$0$4\1v$3@2$2^2@2$1^2^1").

Definition msize_bytes : ltac2:(zQ "20!h8!vg9>2sz$1$0") := ltac2:(zQ "20!vg9!h8\2sz$0M0\2sz$0$1^1N1N2N4N8").

(* [comment removed for export] *)
Definition flat_sc : ltac2:(zQ "50!hk2!h8!np9!mqb!rna>2kn@1$0$2>1a$3>1n$1@1$0$4") := ltac2:(zQ "h50!j6!rna!hk2!js9!poa!jk9!ja!ov3!iob!vh2!ptb!vhc!isa!jk3!h8!pu4!vi4!np9!mqb!le!m7\2kn@1$2$h1\1a$h2\1n$eM8\1x@1$8@2$3$0$0@1$2$1@2$h0^3@1$f^2\1p@2$3$0$0M3\1p@2$3$0$0@1$2$1^1\2lo$0\2hi$0M6\0$6@1$2$1@2$d@2$cZ@2$5^2@1$a^5@2$c@2$5@2$5^1@1$a^5@1$h3^4@2$h4+2+k0@1$4$1@3$7$1@2$9^5@1$b^4@1$4$1@3$7$1@2$9^2@1$b^1@1$4$1").

(* [comment removed for export] *)
Fixpoint wr_covered (allkn kn : list kentry) (a : saddr) (n : nat) : bool :=
  match kn with
  | [] => false
  | KWr (SA kb kk) len :: rest =>
      if (if (expr_eqb (a_base a) kb && Z.leb kk (a_off a))%bool
          then match xlo allkn len with Some l => Z.leb (a_off a + Z.of_nat n) (kk + l) | None => false end
          else false)
      then true
      else if xinside allkn (a_base a) (a_off a) (ELit (Z.of_nat n)) kb kk len then true
      else wr_covered allkn rest a n
  | _ :: rest => wr_covered allkn rest a n
  end.

Definition storeok_sc : ltac2:(zQ "50!hk2!h8!np9!mqb!rna>2kn@1$0$2>1a$3>1n$1@1$0$4") := ltac2:(zQ "a0!rna!ja!hk2!poa!ov3!h8!vj2!vk0!np9!mqb\2kn@1$2$8\1a$9\1n$5M1\0$1@1$2$0@4$6^3^3^2^1@1$3$0@3$4$0@2$7^2^1@1$3$0").

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

(* [comment removed for export] *)
Definition conc_expr : ltac2:(zQ "30!ml1!hk2!np9>2kn@1$1$2>1e$0$0") := ltac2:(zQ "b6!ml1!j6!iob!nkc!tp7!h8!ja!huc!ig2!hk2!np9&M2\1x@1$2$1$0@2$4^5^4\1v$1@1$3^1^4&\1b$0~0&\1a$0~1&\2op$7~2&\2op$8~2&M2\1x@1$2$1$0@2$4^6^5\1v$1@1$3^1^5\2kn@1$9$a\1e$0M0\1e$0$0^1\1z$1^2\1n$5M2\1x@1$2$1$0@2$4^3^2\1v$1@1$3^1^2~3~3~4~4\2sx$6\2lo$5\1n$5\2e0$0~5\2sx$6\1k$5\1i$1\1n$5~5").

(* [comment removed for export] *)
Definition cond_probe : ltac2:(zQ "40!ml1!ja!js9!tq5>1c$3>1a$0>1b$0@2$2$0$1") := ltac2:(zQ "c0!ml1!ome!ja!jub!uma!hv5!hvc!tq5!ulf!tu6!nkc!js9\1c$7\1a$0\1b$0M7\1c$7@2$b$0$2^3@4$3$0$2@3$1$4@3$1$9^2^1@1$a+1$6@4$3$0$2@3$1$4@3$1$9^2^1@1$a+1$5@4$3$0$2@3$1$8^2^1$6@4$3$0$2@3$1$8^2^1$5@4$3$0$2@3$1$4^2^1$6@4$3$0$2@3$1$4^2^1$5").

Definition enum_branch (kn : list kentry) (c : branch_cond) (a b : expr) : option bool :=
  let '(e, pos) := cond_probe c a b in
  match concretize kn e with
  | Some v => let z := Z.eqb (v mod two64) 0 in Some (if pos then negb z else z)
  | None => None
  end.

(* [comment removed for export] *)
Definition to_saddrK : ltac2:(zQ "50!hk2!j6!ml1!np9!mqb>2kn@1$0$3>1e$2>3imm$1$4") := ltac2:(zQ "h26!j6!iob!nkc!ml1!mqb!vkd!kkd!tp7!vl9!qh5!h8!ja!js9!huc!ig2!hk2!np9!vlf&M1\1x@1$1$0$4@2$7^8@3$9$6^7@1$2^6\1v$0@2$8@1$2Z^1@2$5^7^6&\1b$3~0&\1a$3~1&\2op$d~2&\2op$e~2&M1\1x@1$1$0$4@2$7^9@3$9$6^8@1$2^7\1v$0@2$8@1$2Z^1@2$5^8^7\2kn@1$f$h0\1e$3\3imm$0Mc\1x@2$c$3$0$4@1$h1^2\2e0$3\1z$0M3\2e0$3$4^2\2z0$0@2$5^5^4\1n$aM1\1x@1$1$0$4@2$7^6@3$9$6^5@1$2^4\1v$0@2$8@1$2Z^1@2$5^5^4~3~3~4~4\2sx$b\2lo$a\1n$a\2e1$3~5\2sx$b\1k$a\1i$0\1n$a~5").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition amo_sz : ltac2:(zQ "20!vmc!vg9>2wd$0$1") := ltac2:(zQ "40!vmc!vn6!vnd!vg9\2wd$0M0\2wd$0$3^1$1$2").
(* [comment removed for export] *)
Definition amo_sx : ltac2:(zQ "20!ja!vmc>2wd$1$0") := ltac2:(zQ "40!vmc!ja!hv5!hvc\2wd$0M0\2wd$0$1^1$3$2").

(* [comment removed for export] *)
Definition amo_alignedb : ltac2:(zQ "50!ja!hk2!vmc!ml1!np9>2kn@1$1$4>1e$3>2wd$2$0") := ltac2:(zQ "a0!j6!vmc!iob!ja!hv5!hk2!sm7!ml1!np9!kje\2kn@1$5$8\1e$7\2wd$1M2\1x@1$2$0$3@3$6^3^2M1\2wd$1$0^1+2+3\1r$0@2$9^1Z$4").

(* [comment removed for export] *)
Definition resv_inval : ltac2:(zQ "20!iob!mqb>1r@1$0$1>1a$1@1$0@1$0$1") := ltac2:(zQ "f0!iob!mqb!ja!ipa!iq0!pu4!ptb!jk3!qj6!nk0!vo4!nl4!kje!q1!iqe\1r@1$0$1\1a$1M0\1r@1$0$1@1$0@1$0$1^2\2ra$1M2\0$2@1$0@1$0$1@2$a^1^2@2$4@1$0$1@1$3$1M2\0$2@1$0@1$0$1@2$7@2$9@1$5^1@1$5^2@1$8@2$c@2$d@2$e@1$6^1@1$6^2$bZ@2$4@1$0$1^3@1$3@1$0$1@2$4@1$0$1@1$3$1").

(* [comment removed for export] *)
Definition amo_aluop : ltac2:(zQ "30!iob!huc!vp1>2op$2@1$0@1$0$1") := ltac2:(zQ "90!huc!iob!iq0!ipa!vp1!kkd!om3!tg2!vpa\2op$4M4\2op$4@1$1@1$1$0^1@2$2@1$1$0@1$3$0@2$2@1$1$0@2$2$0$5@2$2@1$1$0@2$2$0$8@2$2@1$1$0@2$2$0$6@2$2@1$1$0@2$2$0$7@1$3@1$1$0@1$3@1$1$0@1$3@1$1$0@1$3@1$1$0").

(* [comment removed for export] *)
Definition amo_newval : ltac2:(zQ "60!ml1!hk2!iob!huc!vmc!np9>2kn@1$1$5>2wd$4>3aop@1$2$3>3old$0>3src$0$0") := ltac2:(zQ "80!ml1!iob!huc!vmc!hk2!ur1!vq5!np9\2kn@1$4$7\2wd$3\3aop@1$1$2\3old$0\3src$0M1\3aop@1$1$2$0^3\1o$2M3\2wd$3$0^5@4$6^6^1^3^2@4$5^6^1^3^2^1").

(* [comment removed for export] *)
Definition sym_read (segs : list Segment) (ss : sym_state) (fk : list kentry) (scr : scripts)
           (a : saddr) (n : nat) (sx' : bool)
  : option (expr * list sidecond * scripts * nat) :=
  match log_lookup fk (s_log ss) (a_base a) (a_off a) n sx' (sc_hints scr) [] with
  | LStuck => None
  | LHit v scs hints =>
      Some (extK fk v, flat_sc fk a n ++ scs, SCR (sc_dirs scr) (sc_reads scr) hints, s_next ss)
  | LMiss scs hints =>
      match know_lookupA fk segs (s_know ss) (a_base a) (a_off a) n sx' hints scs with
      | LStuck => None
      | LHit v scs' hints' =>
          Some (extK fk v, flat_sc fk a n ++ scs', SCR (sc_dirs scr) (sc_reads scr) hints', s_next ss)
      | LMiss scs' hints' =>
          (* [comment removed for export] *)
          let i := s_next ss in
          let rv := match sc_reads scr with [] => EVar i | e :: _ => e end in
          let reads' := match sc_reads scr with [] => [] | _ :: t => t end in
          Some (rv, flat_sc fk a n ++ SCReadBase a n sx' rv :: scs', SCR (sc_dirs scr) reads' hints', S i)
      end
  end.

Definition sym_step (segs : list Segment) (i : instr) (ss : sym_state) (scr : scripts) : stepres :=
  let g r := sr_get (s_regs ss) r in
  let p := s_pc ss in
  let fk := facts_of (s_know ss) in   (* [comment removed for export] *)
  match i with
  | OpImm op rd rs imm => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm op rd rs sh => SOk (sset ss rd (mkAluK fk op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op op rd rs1 rs2 => SOk (sset ss rd (mkAluK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | OpImm32 rd rs imm => SOk (sset ss rd (mkAluwK fk ALU_ADD (g rs) (ELit (bv_signed imm))) (p + 4)) [] scr
  | ShiftImm32 op rd rs sh => SOk (sset ss rd (mkAluw op (g rs) (ELit (bv_unsigned sh))) (p + 4)) [] scr
  | Op32 op rd rs1 rs2 => SOk (sset ss rd (mkAluwK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul op rd rs1 rs2 => SOk (sset ss rd (mkMdK fk op (g rs1) (g rs2)) (p + 4)) [] scr
  | Mul32 op rd rs1 rs2 => SOk (sset ss rd (mkMdw op (g rs1) (g rs2)) (p + 4)) [] scr
  | Lui rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12)))) (p + 4)) [] scr
  | Auipc rd imm => SOk (sset ss rd (ELit (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_signed imm) 12 + p)))) (p + 4)) [] scr
  | Jal rd imm => SOk (sset ss rd (ELit (p + 4)) (bv_unsigned (Z_to_bv 64 (p + bv_signed imm)))) [] scr
  | Jalr rd rs1 imm =>
      match conc_expr fk (g rs1) with
      | ELit z => SOk (sset ss rd (ELit (p + 4)) (Z.land (bv_wrap 64 z + bv_signed imm) (-2) mod 2^64)) [] scr
      | _ => SStop
      end
  | Branch c rs1 rs2 imm =>
      let tk := bv_unsigned (Z_to_bv 64 (p + bv_signed imm)) in
      let a := g rs1 in let b := g rs2 in
      match match decide_branch fk c a b with
            | Some t => Some t
            | None => match decide_branch fk c (conc_expr fk a) (conc_expr fk b) with
                      | Some t => Some t
                      | None => enum_branch fk c a b
                      end
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
      let a := to_saddrK fk (g rs) (bv_signed imm) in
      match sym_read segs ss fk scr a n sx' with
      | None => SStop
      | Some (v, scs, scr', nx') =>
          SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                   (s_log ss) (s_know ss) nx' (s_resv ss)) scs scr'
      end
  | Store sz rs1 rs2 imm =>
      let n := msize_bytes sz in
      let a := to_saddrK fk (g rs1) (bv_signed imm) in
      match resv_inval (s_resv ss) a with
      | None => SStop
      | Some r' =>
          SOk (SSR (p + 4) (s_regs ss) (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) r')
              (flat_sc fk a n ++ storeok_sc fk a n) scr
      end
  (* [comment removed for export] *)
  | Lr wd _ _ rd rs =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match sym_read segs ss fk scr a n (amo_sx wd) with
        | None => SStop
        | Some (v, scs, scr', nx') =>
            SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) v)
                     (s_log ss) (s_know ss) nx' (Some a)) scs scr'
        end
      else SStop
  | Sc wd _ _ rd rs1 rs2 =>
      let n := msize_bytes (amo_sz wd) in
      let e := g rs1 in
      if amo_alignedb fk e wd then
        let a := to_saddrK fk e 0 in
        match s_resv ss with
        | Some r =>
            if saddr_eqb r a then
              SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) (ELit 0))
                       (SE a n (g rs2) :: s_log ss) (s_know ss) (s_next ss) None)
                  (flat_sc fk a n ++ storeok_sc fk a n) scr
            else SStop   (* [comment removed for export] *)
        | None => SStop
        end
      else SStop
  | Amo op wd _ _ rd rs1 rs2 =>
      match amo_aluop op with
      | None => SStop
      | Some aop =>
          let n := msize_bytes (amo_sz wd) in
          let e := g rs1 in
          if amo_alignedb fk e wd then
            let a := to_saddrK fk e 0 in
            match resv_inval (s_resv ss) a with
            | None => SStop
            | Some r' =>
                match sym_read segs ss fk scr a n (amo_sx wd) with
                | None => SStop
                | Some (vold, scs, scr', nx') =>
                    SOk (SSR (p + 4) (if bv_eqb rd 0 then s_regs ss else sr_upd (s_regs ss) (ridx rd) vold)
                             (SE a n (amo_newval fk wd aop vold (g rs2)) :: s_log ss) (s_know ss) nx' r')
                        (scs ++ storeok_sc fk a n) scr'
                end
            end
          else SStop
      end
  | _ => SStop
  end.



(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition itab : ltac2:(zQ "00T") := ltac2:(zQ "20!vr0!quc@1$1$0").
Definition itab_lookup : ltac2:(zQ "40!iob!j6!vr0!vr9>1t$3>2pc$1@1$0$2") := ltac2:(zQ "70!vr0!j6!ipa!op9!iob!vr9!qt8\1t$5\2pc$1M1\2pc$1@1$4$0^1@1$2$0\1p$3@3$6$0^3^1\1p$3@1$2$0").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : ltac2:(zQ "20!hk2!rm7@1$0$1").

(* [comment removed for export] *)
Definition itab_entry : ltac2:(zQ "30!iob!j6!vr0>2pc$1@1$0$2") := ltac2:(zQ "e0!vr0!iob!j6!ipa!ja!js9!md!t2!iq0!vv8!hgg6!hgj8!kje!hia\2pc$2M1\1x@1$1@1$7@1$6#i0@1$1$0@2$9?4segs@2$d@1$6#k0^1\1w@1$7@1$6#i0M4\0$4@1$1$0@1$a^1@1$3$0M1\1x@1$1@2$5$0$2@1$1$0@1$b^1\1p@2$5$0$2M5\1p@2$5$0$2@1$1$0^1\1i$0\2sz$2M4\0$4@1$1$0@2$c^1+4@2$8$0^2@1$3$0@1$3$0@1$3$0").
Fixpoint mk_itab_fuel (n : nat) (pc : Z) (t : itab) : itab :=
  match n with
  | O => t
  | S n' => mk_itab_fuel n' (pc + 4)%Z
            (match pc, itab_entry pc with
             | Zpos p, Some i => pt_set p i t
             | _, _ => t
             end)
  end.
(* [comment removed for export] *)
Definition itab_sound : ltac2:(zQ "10!vr9>1t$0P") := ltac2:(zQ "80!vr0!iq0!iob!jge!j6!hgpb!vr9!hgqa\1t$6>2pc$4>1i$0>0@3$3@1$2$0@2$7^3^2@2$1$0^1@3$3@1$2$0@1$5^3@2$1$0^2").
Lemma mk_itab_fuel_sound : ltac2:(zQ "50!hgr9!h8!j6!hgs8!vr9>1n$1>2pc$2>1t$4>0@1$0^1@1$0@3$3^4^3^2").
Proof.
  induction n as [|n IH]; intros pc t Ht; cbn; [exact Ht|].
  apply IH. destruct pc as [|p|p]; try exact Ht.
  destruct (itab_entry (Zpos p)) as [i|] eqn:E; [|exact Ht].
  intros pc' i'. unfold itab_lookup. destruct pc' as [|p'|p']; try discriminate.
  destruct (Pos.eq_dec p' p) as [->|Hne].
  - rewrite pt_gss. intros H; injection H as <-. exact E.
  - rewrite pt_gso by exact Hne. exact (Ht (Zpos p') i').
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition scr_nil : ltac2:(zQ "10!hgt9$0") := ltac2:(zQ "40!poa!ja!hgu4!ml1@3$2@1$0$1@1$0$3@1$0$1").

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition zf_covers : ltac2:(zQ "60!ml1!j6!ja!hk2!h8!np9>5allkn@1$3$5>2rb$0>2rk$1>1n$4>2kb$0>2kk$1>3len$0$2") := ltac2:(zQ "h20!ml1!hv5!h8!j6!ja!huc!ig2!hgub!hk2!ngb!hvc!vhc!np9!hgv7!hhg2!q1!le!m7\5allkn@1$8$c\2rb$0\2rk$3\1n$2\2kb$0\2kk$3\3len$0@2$9M0\3len$0$4^1\2l0$3M7\1x$7$4@6$d^7^6@1$h0^5^4^3@2$f^1@2$h1+2+k0\5delta$3$a$1$1$1\2n0$2$1\2op$5\1a$0\1b$0$1\2op$5\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2op$6\1a$0\1b$0$1\2sx$4\2lo$2\2n0$2\1e$0$1\2sx$4\1k$2\1i$3\2n0$2$1@7$e^7^6^5@1$b^4^3^2^1").

(* [comment removed for export] *)
Definition kentry_overlay : ltac2:(zQ "60!np9!ja!hk2!h8!j6!ml1>5allkn@1$2$0>2rb$5>2rk$4>1n$3>1K$0$1") := ltac2:(zQ "98!mqb!ml1!j6!hv5!ja!hhgd!np9!h8!hk2&\2kk$2@7$5^9^8^7^6^2^1^3&\2kb$1~0&M0\1a$0$4^2~1&\3len$1~2&\1a$0~3&\2kk$2@7$5^a^9^8^7^2^1^4&\2kb$1~5&M0\1a$0$4^3~6\5allkn@1$8$6\2rb$1\2rk$2\1n$7\1K$6M6\1K$6$4^1\1a$0\1w$7\1v$1$3~4\1a$0\3len$1\1k$7~7\2lo$2\2hi$2$3\1e$1\1m$2$3\1e$1\2lo$2\2hi$2$3\1a$0\2n0$1$3\2a1$0\2n1$1\2a2$0\2n2$1$3\1a$0\3len$1\1c$2~7~4").

(* [comment removed for export] *)
Definition segs_avoid : ltac2:(zQ "20!j6!ja>2lo$0>2hi$0$1") := ltac2:(zQ "90!hhhb!j6!rm7!hhi2!isa!ngb!hhie!hhja!jk9\2lo$1\2hi$1@3$7$2\1s$2@2$5@2$4^2@1$0@1$3^1@2$4@2$8@1$0@1$3^1@1$0@1$6^1^3?4segs").
Definition kwr_offimage : ltac2:(zQ "50!ml1!ja!hk2!j6!np9>5allkn@1$2$4>2kb$0>2kk$3>3len$0$1") := ltac2:(zQ "h00!ml1!j6!hv5!ja!h8!js9!jk9!iob!huc!ig2!hk2!hhk5!rv1!np9!q1!m7\5allkn@1$a$d\2kb$0\2kk$1\3len$0M7\1x@1$7@2$5$1$1$3@2$c^4^3\1p@2$5$1$1M5\1p@2$5$1$1$3^1\3blo$1\3bhi$1M0\3len$0$3^4\2l0$1@2$b@2$6^3^6@2$6@2$6^2^6@2$e^1@2$f+2+k0\1n$4$2\2op$8\1a$0\1b$0$2\2op$8\1a$0\1b$0$2\2op$9\1a$0\1b$0$2\2op$9\1a$0\1b$0$2\2sx$3\2lo$4\1n$4\1e$0$2\2sx$3\1k$4\1i$1\1n$4$2$2").

(* [comment removed for export] *)
Definition kentry_readable : ltac2:(zQ "60!np9!ja!hk2!h8!j6!ml1>5allkn@1$2$0>2rb$5>2rk$4>1n$3>1K$0$1") := ltac2:(zQ "h01!ml1!mqb!j6!hhl4!ja!np9!hv5!h8!hgub!le!jk3!hk2!hvc!hhm7!hhgd!hgv7&\1a$1\2n0$0@5$3^7^6^5^4^3\5allkn@1$b$5\2rb$0\2rk$2\1n$7\1K$5M5\1K$5$4^1\1a$1\1w$7\1v$0M1\1a$1$4^3\2kb$0\2kk$2M8\1x$8$4@6$f^9^8@1$9^7^2^1@1$9^4\5delta$2$c$6$6$6~0\1a$1\2n0$0\1k$7@5$3^8^7^6^5^4\2lo$2\2hi$2@5$3^7^6^5^4^3\1e$0\1m$2@5$3^7^6^5^4^3\1e$0\2lo$2\2hi$2@5$3^8^7^6^5^4\1a$1\3len$0M1\1a$1$4^2\2kb$0\2kk$2@2$a@7$e^9^8^7^6^2^1^3@4$d^9^2^1^3\2a1$1\2n1$0\2a2$1\2n2$0@5$3^9^8^7^6^5\1a$1\2n0$0\1c$2@5$3^8^7^6^5^4~0").

(* [comment removed for export] *)
Fixpoint know_byte_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) : bool :=
  match kn with
  | [] => false
  | K :: rest =>
      let lit kb kk (l : Z) := match rel_lit rb rk 1 kb kk l with RInside _ => true | _ => false end in
      (match K with
       | KWord (SA kb kk) w _ => img && lit kb kk (Z.of_nat w)
       | KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KBlob (SA kb kk) (ELit l0) _
       | KUnk (SA kb kk) (ELit l0) => lit kb kk (l0 mod 2 ^ 64)%Z
       | KImg lo hi =>
           img && match rb with
                  | ELit 0 => Z.leb lo rk && Z.ltb rk hi &&
                              match seg_rom segs (Z_to_bv 64 rk) with Some _ => true | None => false end
                  | _ => false
                  end
       | _ => false
       end) || know_byte_cov img rest rb rk
  end%bool.

Fixpoint know_bytes_cov (img : bool) (kn : list kentry) (rb : expr) (rk : Z) (n : nat) : bool :=
  match n with
  | O => true
  | S n' => know_byte_cov img kn rb rk && know_bytes_cov img kn rb (rk + 1) n'
  end.

Definition kn_readable : ltac2:(zQ "60!hk2!np9!ja!h8!j6!ml1>5allkn@1$0$1>2kn@1$0$1>2rb$5>2rk$4>1n$3$2") := ltac2:(zQ "a0!np9!hk2!h8!ngb!hvc!j6!hhn8!hhoc!ml1!hhpf\5allkn@1$1$0\2kn@1$1$0\2rb$8\2rk$5\1n$2@2$3@3$9$0@4$6^5^3^2^1^4@5$7$4^4^3^2^1").
Definition kn_overlay : ltac2:(zQ "60!hk2!np9!ja!h8!j6!ml1>5allkn@1$0$1>2kn@1$0$1>2rb$5>2rk$4>1n$3$2") := ltac2:(zQ "a0!np9!hk2!hv5!h8!ngb!j6!hhl4!hhoc!ml1!hhpf\5allkn@1$1$0\2kn@1$1$0\2rb$8\2rk$5\1n$3@2$4@3$9$0@4$6^5^3^2^1^4@5$7$2^4^3^2^1").

(* [comment removed for export] *)
Fixpoint evars_lt (b : nat) (e : expr) : bool :=
  match e with
  | ELit _ | EBlob _ _ _ _ => true
  | EVar v => Nat.ltb v b
  | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y => evars_lt b x && evars_lt b y
  | EExt _ _ _ x => evars_lt b x
  end.

(* [comment removed for export] *)
Fixpoint find_readbase (i : nat) (scs : list sidecond) : option (saddr * nat * bool) :=
  match scs with
  | [] => None
  | SCReadBase a n sx (EVar j) :: rest => if Nat.eqb j i then Some (a, n, sx) else find_readbase i rest
  | _ :: rest => find_readbase i rest
  end.

(* [comment removed for export] *)
Definition x_dischargeable : ltac2:(zQ "70!ja!js9!mk4!h8!iob!mqb!rna>2ss$2>3ss'$2>2rb@1$4@2$1@2$1$5$3$0>2sc$6$0") := ltac2:(zQ "hf1!ml1!hv5!h8!ja!mqb!jk3!js9!j6!huc!ig2!pu4!lj6!iob!ptb!mo5!rna!hk2!hhqa!np9!mk4!kpe!isa!tq5!hhra!hhs7!hht6!mn2!vo4!hhu2!hhvb!hn2&\2a1$4\2n1$0\2a2$4\2n2$0$1\2ss$h3\3ss'$h3\2rb@1$c@2$6@2$6$4$2$3\2sc$f=2kn@1$h0$h2@1$ha^4=2fk@1$h0$h2@1$h9^1Mf\2sc$f$3^3\5taken$3\1c$h6\1a$0\1b$0$1\1a$4\1n$0M0\1n$0$3^1\1z$7@2$5@2$5@2$h5+1^1@2$h5^1+8@5$h1^4^5@1$a^3@1$d^3@1$he^1\2n0$2$1\2op$8\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\2sx$3\2lo$2\2n0$2\1e$0$1\2sx$3\1k$2\1i$7\2n0$2$1~0~0\1a$4\1n$2@2$5@2$5@2$bN1^1@2$b^1N8@5$h8^3^4@1$a^2@1$d^2^1\1a$4\1n$2\2sx$3\1e$0M0\1e$0$3^1\1z$7$1\1j$2@2$5@2$5@2$5@2$5@2$5@2$5Mc\2rb@1$c@2$6@2$6$4$2$3$3^9\1p@2$6@2$6$4$2$3M6\1p@2$6@2$6$4$2$3$3^1\2p0@2$6$4$2\3sx'$3M6\2p0@2$6$4$2$3^2\2a'$4\2n'$2@2$5@2$5@2$hb^2^a@2$h4^1^9@2$hd^3^8$1@2$h4^1@1$e^b@2$hc^1@1$e^a@2$h7@1$e^b@1$a^5@2$bN1^4@2$b^4N8@5$h1^6^7@1$a^5@1$d^5^4\2op$8\2a0$0\1b$0$1\2op$8\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\2op$9\2a0$0\1b$0$1\3sx0$3\2lo$2\2n0$2\2e0$0$1\3sx0$3\1k$2\1i$7\2n0$2$1\1a$0\1b$0$1").

Definition x_filter : ltac2:(zQ "30!hk2!rna!mk4>2ss$2>3ss'$2>3scs@1$0$1@1$0$1") := ltac2:(zQ "e0!rna!hk2!js9!mk4!ja!h8!qj6!poa!iob!hig3!hih5!mo5!mqb!og8\2ss$3\3ss'$3\3scs@1$1$0M1\3scs@1$1$0@1$1$0^1@1$7$0\1s$0\1l@1$1$0=2rb@1$8@2$2@2$2$c$5$4@2$9@1$b^5^3@3$d$0\2sc$0@1$6@4$a^7^6^2^1^4").

(* [comment removed for export] *)
Fixpoint esize_budget (e : expr) (b : nat) {struct e} : option nat :=
  match b with
  | O => None
  | S b' =>
      match e with
      | ELit _ | EVar _ | EBlob _ _ _ _ => Some b'
      | EAlu _ x y | EAluw _ x y | EMd _ x y | EMdw _ x y =>
          match esize_budget x b' with Some b'' => esize_budget y b'' | None => None end
      | EExt _ _ _ x => esize_budget x b'
      end
  end.
Definition esize_le : ltac2:(zQ "30!ja!h8!ml1>1e$2>1k$1$0") := ltac2:(zQ "70!h8!iob!ja!hv5!hvc!hii9!ml1\1e$6\1k$0M1\1x@1$1$0$2@2$5^2^1\1n$0$4$3").

(* [comment removed for export] *)
Definition rd_of : ltac2:(zQ "40!iob!md!vr0!t2>1i$2@1$0@1$3@1$1#5") := ltac2:(zQ "h6hd!md!t2!ipa!iq0!hija!ja!huc!vmc!vr0!hik2!hikb!vg9!ig2!iob!vp1!tq5!hil6!him0!hima!hin3!hio0!hioa&\3imm@1$1@1$0#h4@2$3@1$1@1$0#5^2&\2rd@1$1@1$0#5~0&\3imm@1$1@1$0#c@2$3@1$1@1$0#5^3&\3rs1@1$1@1$0#5~2&\2rd@1$1@1$0#5~3&\3imm@1$1@1$0#c@1$2@1$1@1$0#5&\3rs2@1$1@1$0#5~5&\3rs1@1$1@1$0#5~6&\3rs2@1$1@1$0#5@2$3@1$1@1$0#5^3&\3rs1@1$1@1$0#5~8&\2rd@1$1@1$0#5~9&\2op$6~a&\3rs1@1$1@1$0#5@1$2@1$1@1$0#5&\2rd@1$1@1$0#5~c&\3rs1@1$1@1$0#5~5&\2rd@1$1@1$0#5~e&\2op$c~a&\2rl$5~a&\2aq$5~h1&\1w$7~h2&\3csr@1$1@1$0#c@1$2@1$1@1$0#5&\2rm@1$1@1$0#3@1$2@1$1@1$0#5&\3rs1@1$1@1$0#5~h5&\2rd@1$1@1$0#5~h6&\3rs2@1$1@1$0#5@1$2@1$1@1$0#5&\3rs1@1$1@1$0#5~h8&\2rd@1$1@1$0#5~h9&\3fmt$4~ha&\3fmt$4~d\1i$8M8\1i$8@1$d@1$1@1$0#5^1~1~1\2rd@1$1@1$0#5\3imm@1$1@1$0#h5@2$3@1$1@1$0#5^2~4\1c$f\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#d@1$2@1$1@1$0#5\2sz$b\6signed$5~4\2sz$b~7\2op$6~4\2op$6\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#6@2$3@1$1@1$0#5^3~b~4\2op$6\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#5@2$3@1$1@1$0#5^3~b\2fm@1$1@1$0#4\4pred@1$1@1$0#4\4succ@1$1@1$0#4~d~f@1$2@1$1@1$0#5@1$2@1$1@1$0#5~h0~h0\1w$7\2aq$5\2rl$5\2rd@1$1@1$0#5\3rs1@1$1@1$0#5@2$3@1$1@1$0#5^2~h3\2op$e~h3\2op$9\2rd@1$1@1$0#5\3rs1@1$1@1$0#5~h4\2op$9\2rd@1$1@1$0#5\4uimm@1$1@1$0#5~h4\3fmt$4~f\3fmt$4~7\2op$h2\3fmt$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3rs3@1$1@1$0#5~h5\2op$h0\3fmt$4\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5~h5\3fmt$4~h7\2op$h5~hb\2op$h3~hb\2op$h1~hb\3dst$a\3src$a~h7\3dir$h4~hc~hc").

(* [comment removed for export] *)
Definition cap_rd : ltac2:(zQ "30!mk4!h8!vr0>1K$1>1i$2>2ss$0$0") := ltac2:(zQ "h90!md!mk4!ja!h8!iob!mo5!ml9!t2!hip4!lk9!vr0!ll5!hip7!hipf!hiqc!mm3!mma!mn2!mnc!mq3!mof!hir6!mp9!lm6!lmb\1K$3\1i$a\2ss$1M3\1K$3$1^3^1\1n$3M4\1x@1$4@1$7@1$0#5$1@1$e^3\2rd@1$7@1$0#5M2\0$2$1@3$b@1$0#5^1@3$h7@1$0#5ZKv$9@2$h8@1$0#5Z^3M2\0$2$1@2$d@2$h5@1$6^3^1^5^3@6$f@1$h3^3@3$h6@1$6^3@1$h0^1@1$c@1$5^3@1$h2^3@1$h1^3@1$8@1$5^3@1$h4^3^2").

Definition sym_stepX : ltac2:(zQ "50!h8!vr0!hgt9!his0!mk4>1K$0>1i$1>2ss$4>3scr$2$3") := ltac2:(zQ "f0!his0!ja!hisb!hgt9!mo5!mk4!hk2!h8!vr0!hit4!hitb!hiu6!hiv3!rna!lj6\1K$7\1i$8\2ss$5\3scr$3M0\1x$0$0@4$c?4segs^3^2^1\3ss'$5\3scs@1$6$d\4scr'$3M1\0$1$0@2$e@1$4^5@1$4^3@3$9@3$a^7^6^3@3$b^5^3^2^1$2$2").

(* [comment removed for export] *)

Fixpoint sym_execTX_go (t : itab) (K : nat) (fuel : nat) (first : bool) (stops : list Z) (ss : sym_state) (ck : sym_state)
  : sym_state :=
  match fuel with
  | O => if s_clean ss then ss else ck
  | S f =>
      if (negb first && existsb (Z.eqb (s_pc ss)) stops)%bool then (if s_clean ss then ss else ck) else
      match itab_lookup t (s_pc ss) with
      | None => if s_clean ss then ss else ck
      | Some i =>
          match sym_stepX K i ss scr_nil with
          | SOk ss' [] _ => sym_execTX_go t K f false stops ss' (if s_clean ss' then ss' else ck)
          | _ => if s_clean ss then ss else ck
          end
      end
  end.

Definition sym_execTX : ltac2:(zQ "60!h8!mk4!ja!hk2!j6!vr9>1t$5>1K$0>4fuel$0>5first$2>5stops@1$3$4>2ss$1$1") := ltac2:(zQ "80!h8!hivf!ja!hk2!j6!hjg6!vr9!mk4\1t$6\1K$0\4fuel$0\5first$2\5stops@1$3$4\2ss$7@7$5^6^5^4^3^2@1$1^1@1$1^1").



End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition kcut (mk : saddr -> expr -> kentry) (kn : list kentry) (wb : expr) (wk : Z) (wn : expr)
           (kb : expr) (kk : Z) (len : expr) : list kentry :=
  let ws := mkAlu ALU_ADD wb (ELit wk) in
  let ks := mkAlu ALU_ADD kb (ELit kk) in
  (* [comment removed for export] *)
  let low :=
    if (if lin_ge0 kn [(kb, kk)] [(wb, wk)] then false   (* [comment removed for export] *)
        else if lin_ge0 kn [(wb, wk)] [(kb, kk)] then lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk)] else false)
    then [mk (SA kb kk) (mkAlu ALU_SUB ws ks)] else [] in
  let high :=
    if (if lin_ge0 kn [(kb, kk); (len, 0%Z)] [(wb, wk); (wn, 0%Z)]            (* [comment removed for export] *)
        then if lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(kb, kk)]                    (* [comment removed for export] *)
             then lin_ge0 kn [(ELit 0, (two64 - 1)%Z)] [(kb, kk); (len, 0%Z)]  (* [comment removed for export] *)
             else false
        else false)
    then let we := mkAlu ALU_ADD ws wn in
         let '(hb, ho) := split_lit we in
         let ha := if (lin_ge0 kn [(hb, ho)] [(wb, wk); (wn, 0%Z)] && lin_ge0 kn [(wb, wk); (wn, 0%Z)] [(hb, ho)])%bool
                   then SA hb ho else SA we 0%Z in
         [mk ha (mkAlu ALU_SUB (mkAlu ALU_ADD ks len) we)]
    else [] in
  low ++ high.

Definition kzero_cut : ltac2:(zQ "40!ml1!hk2!j6!np9>2kn@1$1$3>2wb$0>2wk$2>2wn$0>2kb$0>2kk$2>3len$0@1$1$3") := ltac2:(zQ "60!ml1!j6!hk2!hjh8!hji0!np9\2kn@1$2$5\2wb$0\2wk$1\2wn$0\2kb$0\2kk$1\3len$0@8$3$4^7^6^5^4^3^2^1").
Definition kfill_cut : ltac2:(zQ "40!ml1!j6!hk2!np9>1c$1>2kn@1$2$3>2wb$0>2wk$1>2wn$0>2kb$0>2kk$1>3len$0@1$2$3") := ltac2:(zQ "70!ml1!j6!hk2!hjh8!hji9!np9!mqb\1c$1\2kn@1$2$5\2wb$0\2wk$1\2wn$0\2kb$0\2kk$1\3len$0@8$3\1a$6\1n$0@3$4^2^1^a^7^6^5^4^3^2^1").
Definition kunk_cut : ltac2:(zQ "40!ml1!hk2!j6!np9>2kn@1$1$3>2wb$0>2wk$2>2wn$0>2kb$0>2kk$2>3len$0@1$1$3") := ltac2:(zQ "60!ml1!j6!hk2!hjh8!hjj2!np9\2kn@1$2$5\2wb$0\2wk$1\2wn$0\2kb$0\2kk$1\3len$0@8$3$4^7^6^5^4^3^2^1").

(* [comment removed for export] *)
Definition ktrim : ltac2:(zQ "60!j6!ml1!np9!hk2!h8!mqb>2mk>0$5>0$1$2>2kb$1>2kk$0>2l0$0>1k$0>1w$4@1$3$2") := ltac2:(zQ "h40!np9!j6!ja!hk2!poa!jk9!ov3!nkc!vl9!ml1!iv4!iqe!hjja!h8!mqb!nn2!nn8!q1!le!m7\2mk>0$e>0$9$0\2kb$9\2kk$1\2l0$1\1k$1\1w$d=1l$1@2$h1^3@2$h3+2+k0=3hi1$1@2$h0^3@2$5^5^1=2r1@1$3$0M2\0$2@1$3$0@2$a^6^1@3$6$0@2^8@2$8^7^6@1$7@2$b^1^6@1$4$0@1$4$0=3lo2$1@2$f^7@2$5^5@1$h2^4=2r2@1$3$0M2\0$2@1$3$0@2$a^1@2$5^8^4@3$6$0@2^a@2$8^9^1@1$7@2$b@2$5^8^4^1@1$4$0@1$4$0@3$c$0^3^1").

(* [comment removed for export] *)
Definition kword_cut : ltac2:(zQ "50!h8!j6!ml1!hk2!np9>2kb$2>2kk$1>2w'$0>1v$2>1k$1>1w$0@1$3$4") := ltac2:(zQ "h50!np9!ml1!poa!h8!ja!j6!hk2!hn2!ov3!hv5!hjjf!huc!ig2!hjk6!vl9!hjkf!jk9!iv4!le!iqe!hjja\2kb$1\2kk$5\2w'$3\1v$1\1k$5\1w$3M1\1v$1@1$6$0^3\1z$5=2n1$5@2$h3^3^6=2r1@1$6$0M4\0$4@1$6$0@2$h1Z^1@3$8$0@3$d@2$e^8^7@1$7^1@4$f$9N0@1$7^1^5@1$2$0@1$2$0=1d$5@2$h3@2$h0^5@1$h2^4^8=2r2@1$6$0M4\0$4@1$6$0@2$h1^1@1$h2^8@3$8$0@3$d@2$e^a@2$h0^9^1@2$a^8@1$7^1@4$f$9@1$7^1@2$a^8@1$7^1^7@1$2$0@1$2$0@3$h4$0^3^1\1n$3@1$2$0\2op$b\1a$1\1b$1@1$2$0\2op$b\1a$1\1b$1@1$2$0\2op$c\1a$1\1b$1@1$2$0\2op$c\1a$1\1b$1@1$2$0\2sx$4\2lo$3\1n$3\1e$1@1$2$0\2sx$4\2k0$3\1i$5\1n$3@1$2$0").

(* [comment removed for export] *)
Definition prune_zf : ltac2:(zQ "a1!hk2!np9!ja!js9!ml1!hjl8!j6!rna!h8!mqb&@2$3@2$3@1$0$1@1$0$7@1$0$2>2mk>0$9>0$4$1>5allkn@1$0$1>2wb$4>1k$6>1w$8>1K$1>2kb$4>2kk$6>3len$4>5apart>0$5$2>5hints@1$0$2>8diffbase>0$5~0~0") := ltac2:(zQ "h7h2!hk2!np9!rna!ja!js9!jub!poa!ml1!ov3!hjh8!vhc!jk9!isa!le!h8!j6!hjle!hjl8!huc!ig2!hjm2!nk0!mqb&@2$4@2$4@1$0$1@1$0$2@1$0$3&\0$3~0&@4$5@1$0$1@1$0$2@3$8$1^a@1$6$1@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~2^5&@8$9^f^e^d^c@1$a^b^9^8^7&@4$5@1$0$1@1$0$2~4@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~5^5&M3~1@2$c@2$b^c@1$d^b^8~3~6&\1b$7~7&\1a$7~8&\2op$h2~9&\2op$h3~9&@4$5@1$0$1@1$0$2@3$8$1^b@1$6$1@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~c^6&@8$9^h0^f^e^d@1$a^c^a^9^8&@4$5@1$0$1@1$0$2~e@1$6$2&@4$5@2$4@1$0$1@1$0$2@1$0$3~f^6&M3~1@2$c@2$b^d@1$d^c^9~d~h0\2mk>0$h6>0$7$1\5allkn@1$0$1\2wb$7\1k$f\1w$e\1K$1\2kb$7\2kk$f\3len$7\5apart>0$h1$3\5hints@1$0$3\8diffbase>0$h1~0M3~1@2$h5^6^aM7\3len$7~0^4\2l0$f@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@6$h4^d^7^6^1^a^9@1$6$2^3\1n$eM3~1@2$c@2$b^a@1$d^9^6@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@3$8$1^8@1$6$1@1$6$2^3@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@8$9^d^c^b^a@1$a^9^7^6^5@1$6$2^3~a~a~b~b\2sx$3\2lo$e\1n$e\1e$7~h1\2sx$3\2k0$e\1i$f\1n$e~h1M3~1@1^3$h0@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@3$8$1^7@1$6$1@1$6$2^2M0\1x@1$0$1~0@8$9^c^b^a^9@1$a^8^6^5^4@1^1$h0\2k0$1\1l@1$0$1@4$5@2$4@1$0$1@1$0$2@1$0$3@4$5@1$0$1@1$0$2@3$8$1^2^1@1$6$2^4").

Definition prune1 : ltac2:(zQ "80!hk2!np9!ja!js9!h8!ml1!mqb!rna>5allkn@1$0$1>2wa$6>1w$4>2wv$5>1K$1>5hints@1$0$2@2$3@2$3@1$0$1@1$0$7@1$0$2") := ltac2:(zQ "ibi4!hk2!np9!rna!ja!js9!poa!jub!ml1!mqb!ov3!j6!nkc!iqe!vl9!h8!pu4!jk9!isa!iv4!le!m7!vhc!hjl8!hjmb!huc!ig2!hjnd!nk0!jk3!ngb!op9!hjo9!ptb!kpe!nn8!hjja!hjp1!hji9!hjj2!hji0!hjpe!nn2!q1&@2$4@2$4@1$0$1@1$0$2@1$0$3&@4$6@1$0$1@1$0$2@3$9$1^6@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~1^5&@4$6@1$0$1@1$0$2@1$5$1@1$5$2&\1a$8~0&\0$3~0&@4$6@1$0$1@1$0$2@3$9$1^9@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~6^8&@7$h7^d@1$f^c^7@1$h5^b^3^2^4&\0$h6~8&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^9&@4$6@1$0$1@1$0$2@3$9$1^c@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~b^b&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^b&M3~5@2$h1@2$h0^a@1$h3^e^4~c~d&\1b$7~e&\1a$7~f&\2op$h8~h0&\2op$h9~h0&@4$6@1$0$1@1$0$2@3$9$1^d@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~h3^c&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^c&M3~5@2$h1@2$h0^b@1$h3^f^5~h4~h5&@2^5@2$d@1$bZ^4@1$b@2$c^3^4&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^7&M3~5@2$h2@2$c^3^4@2$h4+2+k0~h7~h8&\1p$he~h9&@2^6@2$d@1$bZ^5@1$b@2$c^4^5&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^8&M3~5@2$h2@2$c^4^5@2$h4+2+k0~hb~hc&\1b$7~hd&\1a$7~he&\2op$h8~hf&\2op$h9~hf&@2^7@2$d@1$bZ^6@1$b@2$c^5^6&M3~5@2$h2@2$c^5^6@2$h4+2+k0~i2~a\5allkn@1$0$1\2wa$8\1w$e\2wv$7\1K$1\5hints@1$0$3=1k$a@1$i0^5=8diffbase>2ka$8>2kl$7~0\2ka$8\2kl$7=5apart$3@7$h7^9@1$f^8^3@1$h5^7@1$f^2@1$i0^2^1M3\5apart$3~0^1~2M0\5hints@1$0$3~0^5@4$6@2$4@1$0$1@1$0$2@1$0$3~3@1$5$3\1b$3\2hs@1$0$3M3\1b$3~0^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^8@1$5$1@3$9$2@4$i8^b@1$h5^a^5^4@1$5$2^1@4$6@2$4@1$0$1@1$0$2@1$0$3~3^1M1\1K$1~0^4\1a$8\2w'$e\1v$7M8~4^3\2kb$7\2kk$aM3~5@2$hb^2@1$f^cM3~5@2$hd@2$h1@2$h0^1@1$h3^4^7@2$h1@2$h0^7@1$h3^b^1~7@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@6$i4^2^1^4^3^7^b@1$5$2^8M3~5@7$h7^d@1$f^c^7@1$h5^b^2^1@1$h5^4~7M3~5@2$hc@2$hc@2$i1^bN1@2$i1^4N1@2$hb^a^3~7@2^6@2$d^2^1@1$h5^4\1a$8\3len$7M8~4^2\2kb$7\2kk$a@c$ha$i7^c@1$f^b^6^a^8^2^1^3~9^7\0$h6@2^6@2$d^3^2^4\1a$8\3len$7\2bk$eM8~4^3\2kb$7\2kk$aM3~5@2$hb^2@1$f^cM7\3len$7~0^4\2l0$a=1l$a@2$ia^1@2$h4+2+k0M3~5@2$hd@2$h1@2$h0^3^1^9@2$h1@2$h0^9@1$h3^d^3@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^b@1$5$1@1$5$2^a@4$6@2$4@1$0$1@1$0$2@1$0$3~3^a\1n$eM3~5@2$h1@2$h0^8@1$h3^c^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^a@1$5$1@1$5$2^9~a~h1~h1~h2~h2\2sx$3\2lo$e\1n$e\1e$7~h6\2sx$3\2k0$e\1i$a\1n$e~h6@2^6@2$d^2^1^4\2lo$a\2hi$aM7\1x$7~0@1$f^9\1z$aMa\1z$a~0^1=2r1@1$0$1M3\0$3@1$0$1@2$h2^3@2$i2^5^2@3$9$1@2$hf^3@2$i2^5^2@1$5$1@1$5$1=3lo2$a@2$i9^4@2$h0^6@1$h3^a=2r2@1$0$1M3\0$3@1$0$1@2$h2^1^4@3$9$1@2$hf^1^4@1$5$1@1$5$1@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$i3$1^3^1@1$5$2^9~ha~ha\1n$eM3~5@2$h2@2$c^2^3@2$h4+2+k0@2^4@2$d@1$bZ^3@1$b@2$c^2^3@4$6@2$4@1$0$1@1$0$2@1$0$3~3^6~i0~i0~i1~i1\2sx$3\3lo0$e\1n$e\1e$7~i3\2sx$3\2k0$e\1i$a\1n$e~i3\1e$7\1m$a~2\1e$7\2lo$a\2hi$a@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^7@1$5$1@1$5$2^6\1a$8\1n$7~2\2a1$8\2n1$7\2a2$8\2n2$7@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^8@1$5$1@1$5$2^7\1a$8\3len$7\1c$aM8~4^3\2kb$7\2kk$a@c$ha\1a$8\1n$7@3$i5^2^1^5^d@1$f^c^7^b^9^2^1^4\0$h6@7$h7^e@1$f^d^8@1$h5^c^3^2^5^8\0$h6@2^7@2$d^3^2^5\1a$8\3len$7M8~4^2\2kb$7\2kk$a@c$ha$i6^c@1$f^b^6^a^8^2^1^3~9^7\0$h6@2^6@2$d^3^2^4").

Fixpoint prune (allkn : list kentry) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1 allkn wa w wv K hints in
      let '(r, scs2, hs2) := prune allkn wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition prune1p : ltac2:(zQ "90!hk2!np9!ja!js9!h8!ml1!mqb!rna!hjq8>5allkn@1$0$1>2sp$8>2wa$6>1w$4>2wv$5>1K$1>5hints@1$0$2@2$3@2$3@1$0$1@1$0$7@1$0$2") := ltac2:(zQ "ici4!hk2!np9!rna!ja!js9!poa!jub!ml1!mqb!ov3!j6!nkc!iqe!vl9!h8!pu4!jk9!isa!iv4!le!m7!vhc!hjl8!hjr1!huc!ig2!hjnd!nk0!jk3!ngb!op9!hjo9!ptb!kpe!nn8!hjja!hjp1!hji9!hjj2!hji0!hjpe!hjq8!nn2!q1&@2$4@2$4@1$0$1@1$0$2@1$0$3&@4$6@1$0$1@1$0$2@3$9$1^6@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~1^5&@4$6@1$0$1@1$0$2@1$5$1@1$5$2&\1a$8~0&\0$3~0&@4$6@1$0$1@1$0$2@3$9$1^9@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~6^8&@8$h7^e^d@1$f^c^7@1$h5^b^3^2^4&\0$h6~8&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^9&@4$6@1$0$1@1$0$2@3$9$1^c@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~b^b&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^b&M3~5@2$h1@2$h0^a@1$h3^e^4~c~d&\1b$7~e&\1a$7~f&\2op$h8~h0&\2op$h9~h0&@4$6@1$0$1@1$0$2@3$9$1^d@1$5$1@1$5$2&@4$6@2$4@1$0$1@1$0$2@1$0$3~h3^c&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^c&M3~5@2$h1@2$h0^b@1$h3^f^5~h4~h5&@2^5@2$d@1$bZ^4@1$b@2$c^3^4&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^7&M3~5@2$h2@2$c^3^4@2$h4+2+k0~h7~h8&\1p$he~h9&@2^6@2$d@1$bZ^5@1$b@2$c^4^5&@4$6@2$4@1$0$1@1$0$2@1$0$3~3^8&M3~5@2$h2@2$c^4^5@2$h4+2+k0~hb~hc&\1b$7~hd&\1a$7~he&\2op$h8~hf&\2op$h9~hf&@2^7@2$d@1$bZ^6@1$b@2$c^5^6&M3~5@2$h2@2$c^5^6@2$h4+2+k0~i2~a\5allkn@1$0$1\2sp$i9\2wa$8\1w$e\2wv$7\1K$1\5hints@1$0$3=1k$a@1$i0^5=8diffbase>2ka$8>2kl$7~0\2ka$8\2kl$7=5apart$3@8$h7^a^9@1$f^8^3@1$h5^7@1$f^2@1$i0^2^1M3\5apart$3~0^1~2M0\5hints@1$0$3~0^5@4$6@2$4@1$0$1@1$0$2@1$0$3~3@1$5$3\1b$3\2hs@1$0$3M3\1b$3~0^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^8@1$5$1@3$9$2@4$i8^b@1$h5^a^5^4@1$5$2^1@4$6@2$4@1$0$1@1$0$2@1$0$3~3^1M1\1K$1~0^4\1a$8\2w'$e\1v$7M8~4^3\2kb$7\2kk$aM3~5@2$hb^2@1$f^cM3~5@2$hd@2$h1@2$h0^1@1$h3^4^7@2$h1@2$h0^7@1$h3^b^1~7@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@6$i4^2^1^4^3^7^b@1$5$2^8M3~5@8$h7^e^d@1$f^c^7@1$h5^b^2^1@1$h5^4~7M3~5@2$hc@2$hc@2$i1^bN1@2$i1^4N1@2$hb^a^3~7@2^6@2$d^2^1@1$h5^4\1a$8\3len$7M8~4^2\2kb$7\2kk$a@c$ha$i7^d@1$f^b^6^a^8^2^1^3~9^7\0$h6@2^6@2$d^3^2^4\1a$8\3len$7\2bk$eM8~4^3\2kb$7\2kk$aM3~5@2$hb^2@1$f^cM7\3len$7~0^4\2l0$a=1l$a@2$ib^1@2$h4+2+k0M3~5@2$hd@2$h1@2$h0^3^1^9@2$h1@2$h0^9@1$h3^d^3@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^b@1$5$1@1$5$2^a@4$6@2$4@1$0$1@1$0$2@1$0$3~3^a\1n$eM3~5@2$h1@2$h0^8@1$h3^c^2@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^a@1$5$1@1$5$2^9~a~h1~h1~h2~h2\2sx$3\2lo$e\1n$e\1e$7~h6\2sx$3\2k0$e\1i$a\1n$e~h6@2^6@2$d^2^1^4\2lo$a\2hi$aM7\1x$7~0@1$f^9\1z$aMa\1z$a~0^1=2r1@1$0$1M3\0$3@1$0$1@2$h2^3@2$i2^5^2@3$9$1@2$hf^3@2$i2^5^2@1$5$1@1$5$1=3lo2$a@2$ia^4@2$h0^6@1$h3^a=2r2@1$0$1M3\0$3@1$0$1@2$h2^1^4@3$9$1@2$hf^1^4@1$5$1@1$5$1@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$i3$1^3^1@1$5$2^9~ha~ha\1n$eM3~5@2$h2@2$c^2^3@2$h4+2+k0@2^4@2$d@1$bZ^3@1$b@2$c^2^3@4$6@2$4@1$0$1@1$0$2@1$0$3~3^6~i0~i0~i1~i1\2sx$3\3lo0$e\1n$e\1e$7~i3\2sx$3\2k0$e\1i$a\1n$e~i3\1e$7\1m$a~2\1e$7\2lo$a\2hi$a@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^7@1$5$1@1$5$2^6\1a$8\1n$7~2\2a1$8\2n1$7\2a2$8\2n2$7@4$6@2$4@1$0$1@1$0$2@1$0$3@4$6@1$0$1@1$0$2@3$9$1^8@1$5$1@1$5$2^7\1a$8\3len$7\1c$aM8~4^3\2kb$7\2kk$a@c$ha\1a$8\1n$7@3$i5^2^1^5^e@1$f^c^7^b^9^2^1^4\0$h6@8$h7^f^e@1$f^d^8@1$h5^c^3^2^5^8\0$h6@2^7@2$d^3^2^5\1a$8\3len$7M8~4^2\2kb$7\2kk$a@c$ha$i6^d@1$f^b^6^a^8^2^1^3~9^7\0$h6@2^6@2$d^3^2^4").

Fixpoint prunep (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(kept, scs1, hs1) := prune1p allkn sp wa w wv K hints in
      let '(r, scs2, hs2) := prunep allkn sp wa w wv rest hs1 in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
Definition ranges_apart_pc (kn : list kentry) (sp : sprep) (b1 : expr) (k1 : Z) (n1 : expr)
           (br2 : option (Z * Z)) (b2 : expr) (k2 : Z) (n2 : expr) : bool :=
  match n1, n2 with
  | ELit z1, ELit z2 =>
      let m1 := zlit64 z1 in let m2 := zlit64 z2 in
      if (match sp_rng sp, br2 with
          | Some (lo1, hi1), Some (lo2, hi2) =>
              (Z.leb (hi1 + k1 + m1) (lo2 + k2) || Z.leb (hi2 + k2 + m2) (lo1 + k1))%bool
          | _, _ => false
          end) then true
      else if in_sides kn (sp_D sp) b2 k2 m2 then true
      else lin_apart kn b1 k1 m1 b2 k2 m2
  | _, _ =>
    if (match sp_rng sp, br2, sp_h1 sp, xhi kn n2 with
        | Some (lo1, hi1), Some (lo2, hi2), Some h1, Some h2 =>
            if (Z.leb (hi1 + k1 + h1) (lo2 + k2) || Z.leb (hi2 + k2 + h2) (lo1 + k1))%bool then true
            else (* [comment removed for export] *)
            if match end_hi kn b1 k1 n1 lo1 hi1 h1 with Some e1 => Z.leb e1 (lo2 + k2) | None => false end then true
            else match end_hi kn b2 k2 n2 lo2 hi2 h2 with Some e2 => Z.leb e2 (lo1 + k1) | None => false end
        | _, _, _, _ => false
        end) then true
    else if in_sides_x kn (sp_Dx sp) b2 k2 n2 then true
    else if negb (shares_var b1 b2) then false
    else if lin_ge0 kn [(b2, k2)] [(b1, k1); (n1, 0%Z)] then true
    else lin_ge0 kn [(b1, k1)] [(b2, k2); (n2, 0%Z)]
  end.

(* [comment removed for export] *)
Definition kbase : ltac2:(zQ "30!iob!ml1!np9>1K$2@1$0$1") := ltac2:(zQ "84!ml1!mqb!j6!iob!ipa!iq0!np9!h8&M1\1a$1@1$3$0^3\2kb$0\5a_off$2@2$5$0^2&M1\1a$1@1$3$0^2\2kb$0\5a_off$2@2$5$0^2&\1n$0~1&\1a$1~2\1K$6M6\1K$6@1$3$0^1\1a$1\1w$7\1v$0~0~3\1a$1\1n$0\1k$7~0\2lo$2\2hi$2@1$4$0\1e$0\1m$2@1$4$0\1e$0\2lo$2\2hi$2@1$4$0\1a$1\1n$0@1$4$0\2a1$1\2n1$0\2a2$1\2n2$0@1$4$0\1a$1\1n$0\1c$2~0~3").

(* [comment removed for export] *)
Definition prune1pc : ltac2:(zQ "b0!hk2!js9!np9!ja!j6!h8!iob!ml1!mqb!rna!hjq8>5allkn@1$0$2>2sp$a>2wa$8>1w$5>2wv$7>1K$2>5hints@1$0$3>3br2@1$6@2$1$4$4@2$1@2$1@1$0$2@1$0$9@1$0$3") := ltac2:(zQ "hbe!hk2!np9!ja!rna!js9!jub!poa!mqb!ml1!j6!pu4!ov3!vhc!hkj0!nk0!hkjb!vl9!h8!jk3!ptb!kpe!iob!hkke!hklb!hkm7!hjpe!hjq8&@2$4@2$4@1$0$1@1$0$3@1$0$2&@4$5@1$0$1@1$0$3@1$6$1@1$6$3&\1a$7~0&\0$2~0&@4$5@1$0$1@1$0$3@3$b$1^a@1$6$1@1$6$3&@4$5@2$4@1$0$1@1$0$3@1$0$2~4^9&@9$f^e^d@1$a^c^6@1$c^b^7^2^1^3&@4$5@1$0$1@1$0$3@3$b$1^9@1$6$1@1$6$3&@4$5@2$4@1$0$1@1$0$3@1$0$2~7^8&\1x@1$0$1~0&@4$5@1$0$1@1$0$3@3$b$1^2^1@1$6$3&@4$5@2$4@1$0$1@1$0$3@1$0$2~a^a&\1l@1$0$1~b&\2k0$1~c\5allkn@1$0$1\2sp$ha\2wa$7\1w$h1\2wv$8\1K$1\5hints@1$0$2\3br2@1$h5@2$4$9$9=1k$9@1$h3^6=8diffbase>2ka$7>2kl$8~0\2ka$7\2kl$8=5apart$2@9$f^b^a@1$a^9^3@1$c^8^4@1$a^2@1$h3^2^1M2\5apart$2~0^1@4$5@2$4@1$0$1@1$0$3@1$0$2@4$5@1$0$1@1$0$3@3$b$1^7@1$6$1@1$6$3^6M0\5hints@1$0$2~0^6@4$5@2$4@1$0$1@1$0$3@1$0$2~1@1$6$2\1b$2\2hs@1$0$2M2\1b$2~0^2@4$5@2$4@1$0$1@1$0$3@1$0$2@4$5@1$0$1@1$0$3@3$b$1^9@1$6$1@3$b$3@4$h9^c@1$c^b^5^4@1$6$3^1@4$5@2$4@1$0$1@1$0$3@1$0$2~1^1M1\1K$1~0^5\1a$7\2w'$h1\1v$8M7~2^3\2kb$8\2kk$9M2~3@2$e^2@1$a^d@7$d^f^e^d^c^b^a^9M2~3@9$f^f^e@1$a^d^7@1$c^c^8^2^1@1$c^4~5M2~3@2$h2@2$h2@2$h4^cN1@2$h4^4N1@2$e^b^3~5@2^6@2$h0^2^1@1$c^4\1a$7\3len$8M7~2^2\2kb$8\2kk$9M2~3@2$e^2@1$a^c@7$d^e^d^c^b^a^9^8M2~3~6~8M0~9@7$h8^e@1$a^c^6@1$c^b^2^1^3@2^5@2$h0^2^1^3~d\1a$7\3len$8\2bk$h1M7~2^3\2kb$8\2kk$9M2~3@2$e^2@1$a^d@7$d^f^e^d^c^b^a^9@2^6@2$h0^2^1^4\2lo$9\2hi$9@7$d^c^b^a^9^8^7^6\1e$8\1m$9@7$d^c^b^a^9^8^7^6\1e$8\2lo$9\2hi$9@7$d^d^c^b^a^9^8^7\1a$7\1n$8@7$d^c^b^a^9^8^7^6\2a1$7\2n1$8\2a2$7\2n2$8@7$d^e^d^c^b^a^9^8\1a$7\3len$8\1c$9M7~2^3\2kb$8\2kk$9M2~3@2$e^2@1$a^d@7$d^f^e^d^c^b^a^9M2~3@9$f^f^e@1$a^d^7@1$c^c^8^2^1^4~5M0~9@8$h6^3^f@1$a^d^7@1$c^c^2^1^4@2^6@2$h0^2^1^4\2k0$1\1l@1$0$1@4$5@2$4@1$0$1@1$0$3@1$0$2~a^b\1a$7\3len$8M7~2^2\2kb$8\2kk$9M2~3@2$e^2@1$a^c@7$d^e^d^c^b^a^9^8M2~3~6~8M0~9@7$h7^e@1$a^c^6@1$c^b^2^1^3@2^5@2$h0^2^1^3~d").

Fixpoint br_lookup (c : list (expr * option (Z * Z))) (b : expr) : option (option (Z * Z)) :=
  match c with
  | [] => None
  | (b', r) :: rest => if expr_eqb b b' then Some r else br_lookup rest b
  end.

Fixpoint prunepc (allkn : list kentry) (sp : sprep) (wa : saddr) (w : nat) (wv : expr) (kn : list kentry) (hints : list bool)
  (cache : list (expr * option (Z * Z))) : list kentry * list sidecond * list bool :=
  match kn with
  | [] => ([], [], hints)
  | K :: rest =>
      let '(br2, cache') :=
        match kbase K with
        | Some kb => match br_lookup cache kb with
                     | Some r => (r, cache)
                     | None => let r := base_range allkn kb in (r, (kb, r) :: cache)
                     end
        | None => (None, cache)
        end in
      let '(kept, scs1, hs1) := prune1pc allkn sp wa w wv K hints br2 in
      let '(r, scs2, hs2) := prunepc allkn sp wa w wv rest hs1 cache' in
      (kept ++ r, scs1 ++ scs2, hs2)
  end.

(* [comment removed for export] *)
End FPX_4.





End AX2.
(* [comment removed for export] *)
