(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocBlocks MallocFacts_B.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B3 F_ntf_D F_ntf_E F_ntf_F F_ntf_G F_ntf_H.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocFacts_Bpres.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~04aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdMallocFacts_B~~~~~~k48gmeta_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocKit_B3~~~~~~p55mw_ok0cget_meta_rec06mstate37Corelib7Numbers7BinNumsv84Npos35stdpp9bitvectorbdefinitionshh82bv07mapinfov81Zv81N37Corelib4Init5Logichkc2eqhkc3and06region37Corelib4Init9Datatypeshn54prod04ghdr35stdpp7numbers1Nhpb6eq_dechn56option25stdpp9countablehs0bN_countable35stdpp7numbers1Zhu06eq_dechn53fst79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~ig22wzhn54Some46Stdlib6ZArith6BinInt1Zil22lt25stdpp4basein06lookuphs0bZ_countablehs0eprod_countable25stdpp9decidableiq7bprod_eq_dec25stdpp4gmapis74gmapis7bgmap_lookuphn53sndhkc2exhkc3not07RKGroup04conc06r_kind05r_len05rkind0bround_up_pg08s_groups09s_regionsil23pow06r_baseil23add79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jlb2wail22le07Unknown09cell_read07cellval0aget_shadowil26modulo79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent5F_ntf~~~~~~jt49oracle_ok08s_shadow06shadow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~kj13mem79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~knb3rdvkj18pans_mem05Known" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma gmeta_mw : ltac2:(zQ "50!je!oa!ta!u2!v0>2st$4>1g$0>1p$0>0@3$1^3^2^1@1$2@2$3^4^3").
Proof. intros st g p.
  intros GO. pose proof (go_li _ _ _ GO). pose proof (go_freeable _ _ _ GO). pose proof (go_sc _ _ _ GO). pose proof (go_maplen _ _ _ GO).
  unfold mw_ok. repeat split; lia.
Qed.

Lemma ntf_unfold {R} (dec : decoder R) f st g i (k : mstate -> mapinfo -> Malloc.M R) bail :
  nontrivial_free dec (S f) st g i k bail =
  let mr := get_meta_rec st g in
  let sc := m_sizeclass mr in
  if ntf_cond st g i then
    match m_next mr with
    | Some _ =>
      guard 50 (sc <? 48) (
        let activate_new := optr_eqb (active st sc) (Some g) in
        let st1 := dequeue (LActive sc) g st in
        match activate_new, active st1 sc with
        | true, Some a => activate_group a st1 (fun st2 _ => free_group R dec (nontrivial_free dec f) st2 g k bail) bail
        | _, _ => free_group R dec (nontrivial_free dec f) st1 g k bail
        end) bail
    | None => free_group R dec (nontrivial_free dec f) st g k bail
    end
  else if Z.lor (m_freed mr) (m_avail mr) =? 0 then
    guard 51 (sc <? 48) (
      if negb (optr_eqb (active st sc) (Some g)) then queue (LActive sc) g st (fun st0 => k (aor_st st0 g i) None) bail
      else k (aor_st st g i) None) bail
  else k (aor_st st g i) None.
Proof. reflexivity. Qed.

Lemma free_group_unfold {R} (dec : decoder R) rec st g (k : mstate -> mapinfo -> Malloc.M R) bail :
  free_group R dec rec st g k bail =
  let mr := get_meta_rec st g in
  let st1 := fg_usage_st st g in
  match m_mem mr with
  | None => SVis (EUndef UBadPtr) (fun _ => bail)
  | Some p =>
    let st1 := del_slots p (get_stride mr) (m_last_idx mr + 1) (del_group p st1) in
    if negb (m_maplen mr =? 0) then
      free_meta g (record_seq (m_sizeclass mr) (step_seq st1)) (fun st3 => k st3 (Some (p, m_maplen mr * 4096))) bail
    else
      dec st1 p (fun m idx => rec st1 m idx (fun st3 mi => free_meta g st3 (fun st4 => k st4 mi) bail) bail) bail
  end.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition ntf_result : ltac2:(zQ "40!hh1!hj5!hjb!v0>3st'$3>2mi$2>3a0v@1$1@1$0#k0>3a1v@1$1@1$0#k0P") := ltac2:(zQ "i60!hk4!hk8!hm0!hm6!hmd!hod!je!hp5!hqc!hh1!hj5!hr6!ht1!hv1!hvb!ik4!ika!ima!inc!io6!ip5!ir8!it3!itb!iua!iv1!iv7!ive!jg7!hjb!v0!jgd!jh5!jhc!ji3!jj0!jja!jk5\3st'$he\2mi$hd\3a0v@1$a@1$9#k0\3a1v@1$a@1$9#k0Mb\2mi@1$b@2$5$6$0P^3\1p@2$5$6$0M5\1p@2$5$6$0P^1\1b$6\3len$0@2$3@3$2@1$a@1$9#k0^5@1$f@2$hc^7^2@2$3@3$2@1$a@1$9#k0^4@1$f^1@2$3@2$3@2$h1Z^1@2$h1^1@2$i5+2+k0@2$3@3$2$0@3$h8$1$0^2Z@2$3@2$h9$4\1r$4@2$3@3$2@1$b$4@6$h2$1$4@4$h6$1$8$c$4@4$h7$1$8$c$4@3$e$1$0^3@1$i4^8@2$h0$4^1@2$3@3$2$i1@1$hf^1$hb@3$2$0^2@1$i2@1$i0^1>2b'@2$5$1$0>2gh$7>0@3$2@1$b$7@6$h2@2$5$1$0$7@4$h6$6@4$h5$1$8$0$d@6$h4$1$8$c$0$d$h3$7@4$h7$6@4$h5$1$8$0$d@6$h4$1$8$c$0$d$h3$7^2@1$i3^9@2$h0$7^1@1$ha@3$2$1@3$e$1$0^3@3$e$1$0^5@3$2@1$a@1$9#k0^1@1$fZ").

(* [comment removed for export] *)
Definition oracle_ok : ltac2:(zQ "41!hh1!hj5!hr6!v0&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1o~0>1m~0>2st$3P") := ltac2:(zQ "hf1!hmd!hh1!hj5!hr6!hm0!hk8!jkc!jl4!hk4!jp5!jpb!ht1!hqc!ika!hm6!ive!jq1!jqa!jr5!jre!v0!jgd!jh5!jhc!ji3!jja!ima!jsa!inc!it3!itb&>0@1$2@1$1#k0@1$3@1$2@1$1#8\1o~0\1m~0\2st$h4>3rid$5>1r$0>1q$8>1h$8>0@3$4@1$3$0@6$hc$5$0@4$hd$5$c$b$0@4$he$5$c$b$0^4@1$h9^5@2$d$0^3>0@3$4$h7@1$h5^4$f>0@2$e@2$aZ^4@2$ha^4@1$h8@1$h6^5>0@2$a+8@2$hb@2$7@1$6^6^5+h0>0@3$4$h2@2$h1@2$h3^9^8^6@1$h0^5@3$4@1$3@1$2@1$1#8@1^c@1$9@2$7@1$6^8^7@1^b@1$9@2$7@1$6^8^7").

Lemma oracle_ok_frame : ltac2:(zQ "e1!hh1!hj5!hr6!hm0!hk8!kh2!v0!jja!khf!ht1!it3!hqc!hmd!ki9&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1o~0>1m~0>2st$6>3st'$6>0@3$5^4^3^2>0@3$3@4$a$4$b$9$c@1$7^2@1$7^3>0@3$3@4$a$4$b$9$d@1$8^3@1$8^4@3$5^7^6^4").
Proof. intros o m st st'.
  intros OK ER ES rid r q h Hr Hk Hq M8 Hc. rewrite ER in Hr. unfold get_shadow in Hc. rewrite ES in Hc.
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma rdv_known : ltac2:(zQ "e0!hk4!hk8!hm0!kn4!hvb!hod!iua!ks5!ksc!kt8!jqa!jr5!jre!v0>1o$3>2st$d>1q@2$5$1$0>1v$0>0@3$2$b@2$a@2$c^3@3$4$1$0^2@3$6$1$0^2@1$9^1@3$2$0@5$7$3$8^5^4^3^2").
Proof. intros o st q v. intros H. unfold rdv. rewrite H. reflexivity. Qed.

Section NTF.
Variables (ra0 : word) (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (o : word -> option byte) (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
End NTF.
(* [comment removed for export] *)
