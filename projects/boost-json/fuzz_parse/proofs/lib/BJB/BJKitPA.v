(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AsConst AsIface AsCXXHeap CXXRep CXXLib AsObj.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJB Require Import BJRep AXpres BJKitVS.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB5BJRep~~~~~~hc6pstate79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs7AsIface~~~~~~m13mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~q44cell04Npos37Corelib4Init9Datatypesud4cons35stdpp9bitvectorbdefinitionshgc2bv37Corelib4Init5Logichif3andq42C8ud4list79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~hl62wz46Stdlib6ZArith6BinInt1Zhp73addud3nilhif2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~hs25asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ig68rw_cellsq42C1hif2eqhl62b8q42CBud6lengthud3natud4boolhgcbbv_unsignedhp72leud5falsehif3iffhif3nothc8ps_depthhc8ps_ecsethc6ps_endhc7ps_more89OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJKitPA3HCW~~~~~~isdcparser_cellshc9parser_athc5ps_vshc5vs_atud6optionq4acells_sizehp76of_natm15block36Stdlib5Lists4Listjm32Inud4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3BJB7BJKitVS~~~~~~jo3dX_above_hceiljo3cblocks_belowhc9blocks_vs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs6CXXRep~~~~~~juedxclient_rangejue5xpres79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kk4ddisjoint_fromkk43ivlkk45munchkk45wmonohcabj_staticsud3fst37Corelib5Lists7ListDefkrd6Forallhs28AIMG_TOPm13asr" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HCW.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!kua$0").

  (* [comment removed for export] *)
  Definition parser_cells : ltac2:(zQ "30!h9!l8!pe>1m$2>1a$0>2ps$1P") := ltac2:(zQ "i00!u0!u7!hg5!hi9!hk3!hka!hkf!hp1!hqf!hr6!hrc!hvd!ik1!ikd!il2!il8!ile!im3!imc!in2!h9!in9!io8!ioe!ip6!ipd!iq4!iqf!ira!is3!l8!pe\1m$hf\1a$h4\2ps$he@2$4@2$a@1$6@1$3@1$1#8\3num@1$6@1$3@1$1#8@2$4@3$e$h2@2$h1@1$3@1$1#8^1Nh8@4$c$b^4@2$8^3+k0@3$2$0@2$h0Nh8^1@1$9$0@2$4@2$a@1$3@1$1#k0\5ecval@1$3@1$1#k0@2$a@1$3@1$1#k0\5eccat@1$3@1$1#k0@2$a@1$3@1$1#k0\3lcf@1$3@1$1#k0@2$4@4$c$b^6@2$8^5+l8@3$2$0@1$5^3@3$2$0@1$5^2@3$2$0@1$5^1@1$9$0@2$4@2$h8@3$e$h3@1$hb^4$h7@3$e@1$3@1$1#k0^1@1$7Z@1$h9@3$e$h4@2$h5@1$1#k0^1+1@2$4@4$c$b^3@2$8^2+n0@3$2$0@1$5@1$7Z@3$2$0@1$5@1$7Z@3$2$0@1$5@1$7Z@3$2$0@1$5@1$7Z@3$2$0@1$5@1$7Z@3$2$0@1$5@1$7Z@1$9$0@2$4@2$a@1$6@1$3@1$1#8\7scratch@1$6@1$3@1$1#8@2$4@3$e$h2@2$h1@1$3@1$1#8^1Nh0@4$c$b^4@2$8^3+q0@3$2$0@2$h0Nh0^1@1$9$0@2$4@2$a@1$3@1$1#8\4done@1$3@1$1#8@2$a@1$3@1$1#8\5clean@1$3@1$1#8@2$a@1$6@1$3@1$1#8\4pad5@1$6@1$3@1$1#8@2$4@2$4@3$e$h2@2$h1@1$3@1$1#8^1N5@2$4@2$h6@2$h5@1$1#8^3+1@2$h6@2$h5@1$1#8^2+1@4$c$b^6@2$8^5+r0@3$2$0@1$d@1$fMh3\0$h3$h4@1$hd^4+1Z@3$2$0@1$d^3@3$2$0@1$d^2@3$2$0@2$h0N5^1@1$9$0@2$4@4$c$b^3@2$8^2+r8@3$2$0@1$5@1$7@1$hc^1@1$9$0@2$4@2$a@1$6@1$3@1$1#8\2nb@1$6@1$3@1$1#8@2$4@3$e$h2@2$h1@1$3@1$1#8^1Ni8@4$c$b^4@2$8^3+s0@3$2$0@2$h0Ni8^1@1$9$0@2$4@4$c$b^3@2$8^2+u8@3$2$0@1$5@1$7@2$8^2+s0@3$2$0@1$5@1$7Z@1$9$0@2$4@2$a@1$6@1$3@1$1#8\4pad2@1$6@1$3@1$1#8@4$c$b^4@2$8^3+v8@3$2$0@1$5@1$7+i0@3$2$0@1$d@1$fZ@3$2$0@1$d@1$fZ@3$2$0@1$d@1$fZ@3$2$0@1$d@1$fZ@3$2$0@1$d@1$fZ@3$2$0@1$d@1$fZ@3$2$0@2$h0N2^1@1$9$0@2$4@4$c$b^3@2$8^2+hg8@3$2$0@1$5@1$7@1$ha^1@1$9$0@2$a@1$6@1$3@1$1#8\2j8@1$6@1$3@1$1#8@2$4@3$e$h2@2$h1@1$3@1$1#8^1N8@4$c$b^4@2$8^3+hh0@3$2$0@2$h0N8^1@1$9$0").

  Lemma parser_at_split : ltac2:(zQ "b0!hk3!iq4!io8!ip6!h9!jgf!jhf!jib!l8!jj3!pe>1m$a>1a$4>2ps$8@2$3@4$6?5HCEIL^3^2^1@2$0@4$9?5HCEIL^3^2@1$7^1@2$0@3$5^3^2^1@2$0@2$2Z@1$1^1@2$2@1$1^1+i0").
  Proof.
    intros m a ps. unfold parser_at, parser_cells. tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma parser_cells_transport : ltac2:(zQ "e1!u7!hi9!hqf!jjb!h9!jgf!hvd!ik1!io8!hkf!l8!u0!jk4!jl1&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1m~0>2m'~0>1a$4>2ps$a>0>1A$4>2cs@1$9$b>0@4$7$6^6^2^1>0@2$8@2$2^5+k0^3>0@2$8@2$2^4@1$d@1$c^3@2$2^6+hh8@4$7$6^8^5^4>0@3$5^5^3^2@3$5^5^4^3").
  Proof.
    (intros m m' a ps TR nd_i1; ndestruct nd_i1 as (NUM & ECC & STZ & SCR & MOREC & ENDC & NB & NBP & OPT & DEPC & LITC)).
    assert (T : forall A cs, rw_cells asegs m A cs -> a + 64 <= A -> A + Z.of_nat (cells_size cs) <= a + 280 -> rw_cells asegs m' A cs) by exact TR.
    split. { ndestruct NUM as (num & Ln & Rn). exists num. split; [exact Ln|]. apply T; [exact Rn| lia| cbn; lia]. }
    split. { ndestruct ECC as (e1 & e2 & e3 & Re & Hiff & Hne1). nexists e1, e2, e3. split; [| split; [exact Hiff| exact Hne1]]. apply T; [exact Re| lia| cbn; lia]. }
    split. { apply T; [exact STZ| lia| cbn; lia]. }
    split. { ndestruct SCR as (sc & Ls & Rs). exists sc. split; [exact Ls|]. apply T; [exact Rs| lia| cbn; lia]. }
    split. { ndestruct MOREC as (dn & cl & p5 & Lp & Rm). nexists dn, cl, p5. split; [exact Lp|]. apply T; [exact Rm| lia| cbn; lia]. }
    split. { apply T; [exact ENDC| lia| cbn; lia]. }
    split. { ndestruct NB as (nb & Lb & Rb). exists nb. split; [exact Lb|]. apply T; [exact Rb| lia| cbn; lia]. }
    split. { apply T; [exact NBP| lia| cbn; lia]. }
    split. { destruct OPT as (pd2 & Ro). exists pd2. apply T; [exact Ro| lia| cbn; lia]. }
    split. { apply T; [exact DEPC| lia| cbn; lia]. }
    ndestruct LITC as (j8 & Lj & Rl). exists j8. split; [exact Lj|]. apply T; [exact Rl| lia| cbn; lia].
  Qed.

  (* [comment removed for export] *)
  Lemma parser_at_xpres : ltac2:(zQ "e0!h9!jlb!hkf!jhf!pe!jn6!jnc!js1!jt2!ju2!jib!l8!kia!kjb>2LB@1$2$1>2SP$0>1X@1$2@2$6$0$0>1m$4>2m'$4>1a$0>2ps$b>0@7$d?5HCEIL?1H^7^6^5^4^3>0@3$7?5HCEIL?1H^6>0@3$8?5HCEIL?1H^9>0>1b$1>0@3$5$1^1@1$9@1$a^5@3$5$1^2^c>0@7$c?5HCEIL?1H^b^a^9^6+hh8>0@4$3?5HCEIL^9^7^6@4$3?5HCEIL^9^8^7").
  Proof.
    intros LB SP X m m' a ps XP HX HB SUB XC PA.
    apply parser_at_split in PA. ndestruct PA as (VS & PC & DR). apply parser_at_split.
    split; [| split; [| exact DR]].
    - eapply vs_at_xpres; [exact XP| exact HX| exact HB| exact SUB| | exact VS].
      destruct XC as [AC FX]. split; [eapply aclient_range_sub; [exact AC| lia| lia| lia]|].
      eapply Forall_impl; [| exact FX]. intros iv K. cbn in K |- *. lia.
    - eapply parser_cells_transport; [| exact PC]. intros A cs R H1 H2.
      eapply xpres_rw_cells; [exact XP| exact R|].
      destruct XC as [AC FX]. split; [eapply aclient_range_sub; [exact AC| lia| lia| lia]|].
      eapply Forall_impl; [| exact FX]. intros iv K. cbn in K |- *. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma parser_at_munch : ltac2:(zQ "e1!u7!hi9!jjb!jhf!hkf!h9!jib!l8!jj3!hvd!ko0!kp1!kp8!kq1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1W@1$4$b>1m~0>2m'~0>1a$5>2ps$7>0@3$c^5^4^3>0@3$d$9^5^4>0@3$a^7^4+hh8>0@4$8?5HCEIL^6^5@1$6^4>0@4$3?5HCEIL^8^6^5@4$3?5HCEIL^8^7^6").
  Proof.
    intros W m m' a ps MU WM DJ VS PA.
    apply parser_at_split in PA. ndestruct PA as (_ & PC & DR). apply parser_at_split.
    split; [exact VS| split; [| exact DR]].
    eapply parser_cells_transport; [| exact PC]. intros A cs R H1 H2.
    eapply rw_cells_transport; [exact R| exact MU| exact WM|]. eapply disjoint_from_sub; [exact DJ| lia| lia].
  Qed.
End HCW.

(* [comment removed for export] *)
Section ST.
  Context {HCEIL : HeapCeil}.
  Lemma bj_statics_frame : ltac2:(zQ "h00!h9!jnc!u7!kqa!hi9!kr7!hkf!jjb!kt4!kte!hvd!pe!kp1!kp8!kq1!io8>1W@1$6$c>1m$b>2m'>0@1$4@1$2#k0@1$7@1$4@1$2#8>0@1$3^2>0@3$d^4^3^2>0@3$e$a^4^3>0@3$8@2$1$0$0\2iv@2$1$0$0@2$f$9@3$5$0$0^1^6@1$3^5").
  Proof.
    intros W m m' BS MU WM FW.
    assert (DJ : forall a n, a + n <= AIMG_TOP -> disjoint_from W a n).
    { intros a n Hn. clear - FW Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|]. inversion FW; subst. cbn in *.
      split; [lia| apply IH; assumption]. }
    ndestruct BS as (B1 & B2 & B3 & (salt & B4) & B5 & B6).
    unfold bj_statics, BJ_INSTANCE, BJ_DR_VTBL, BJ_ARR_EMPTY, BJ_OBJ_EMPTY, BJ_ERRCAT, BJ_ERRCAT_VTBL, AIMG_TOP in *.
    repeat match goal with |- _ /\ _ => split end; try (eexists salt);
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM| apply DJ; cbn; lia]).
  Qed.
End ST.
