(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XHoare
  XFPSteps XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4boolhc4list36Stdlib5Lists4Listk27existsb46Stdlib6ZArith6BinInt1Zlf3eqb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~nd5sstephc3app99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XSegAuto23SA28WithSegs~~~~~~sb3inbhc4consnd7SFsdSeqnd6SBlocknd5SCopynd5SFillnd7SFldSeq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hl19sym_statend4wenthc6optionhc4prod04Npos35stdpp9bitvectorbdefinitionshs02bvhc4None3h5LinuxProcessSemantics5Riscv5Instrhua4ffmthua5aluophua5instrhua6awidthhua6fmvdirhua5csrophua7fcvt_tyhua5msizehua5mulophl14s_pchc4Somehc4negbhc3nilhc4pairhua5amoophuabbranch_condhua6fariophua6fcmpophua5fmaophua9fminmaxophua6fsgnophl13SSRhl1bitab_lookuphl16s_knowhl16s_nexthl16s_regshl15saddrhl16sentrynd6closedlf3addsb4picksbastep_fmvdxnd8seg_stephl14exprhc3nat37Corelib5Lists7ListDefjl43nthhl14ELithl16two63zhl15two64lf3leblf3subhl16kentryhc5falsehc4andblf6of_nathl15s_logsbadead_belowsb8sp_belowk26filtersb5prune37Corelib4Init5Logicjud3andjud2eqk22Innd3INV3h5LinuxProcessSemantics5Riscv7Preludekh95bvmaphl13envnd8step_reqjud2ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~km07FPStatekm06fp_csrkm04mkstkm07seg_romnd4wdenhs07Z_to_bv37Corelib4Init5Peanokt92le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun3~~~~~~kv39env_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~lk06mstepshc4truesb8seg_auto3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypelp97Segmenthl14itabhl1aitab_sound89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX~~~~~~luf9copy_specluf9fill_spec" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import SR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SA2.
Section WithSegs.
Variable segs : ltac2:(zQ "20!jb!lse@1$0$1").
Variable IT : ltac2:(zQ "10!lt9$0").
Variables x_cpy x_set : Z.
Variable fsd_pcs fld_pcs : list Z.
Variable fsd1_pcs fmv_pcs : list Z.   (* [comment removed for export] *)
Variable BFUEL : nat.

Definition inb : ltac2:(zQ "30!h9!j4!jb>1z$0>1l@1$2$0$1") := ltac2:(zQ "40!h9!jb!l5!n7\1z$0\1l@1$1$0@3$2$0@1$3^2^1").

Definition pick : ltac2:(zQ "30!h9!jb!rd>4ends@1$1$0>2pc$0$2") := ltac2:(zQ "d0!j4!h9!rd!s5!hh7!hhd!hi4!n7!jb!hie!hj7!hjf!hk7\4ends@1$8$1\2pc$1M0\0$0$2@2$7^1?5x_cpy$aM0\0$0$2@2$7^1?5x_set$bM0\0$0$2@2$4^1?7fsd_pcs@1$6Ni0M0\0$0$2@2$4^1?7fld_pcs@1$cNi0M0\0$0$2@2$4^1?8fsd1_pcs@1$6N1@1$9@3$5$1?5x_cpy@3$5$1?5x_set@3$3$1?7fsd_pcs@3$3$1?7fld_pcs@3$3$1?8fsd1_pcs@3$3$1?7fmv_pcs^2").

(* [comment removed for export] *)
Definition step_fmvdx : ltac2:(zQ "50!jb!hp6!hq3!hqa!hr3>2ss$1>1w@1$0$2@1$3@2$4$1@1$0$2") := ltac2:(zQ "i7h6!hra!htd!jb!hp6!hq3!hr3!hu3!ige!j4!hqa!ih6!ihf!ii8!ij2!ijc!ik5!il0!il9!im2!ima!in1!in8!ine!io5!ioe!ipd!iq7!ir1!ira!is7!it1!it8!iu7!iv1!ivb!jg5!jge!jh8!ji1&\3imm@1$1@1$0#h4@1$6@2$5$3@1$2$4&\2rd@1$1@1$0#5~0&\3imm@1$1@1$0#c@1$6@2$5$3@1$2$4&\3rs1@1$1@1$0#5~2&\2rd@1$1@1$0#5~3&\3rs2@1$1@1$0#5~2&\3rs1@1$1@1$0#5~5&\3rs2@1$1@1$0#5@1$6@2$5$3@1$2$4&\3rs1@1$1@1$0#5~7&\2rd@1$1@1$0#5~8&\2op$a~9&\3rs1@1$1@1$0#5@1$6@2$5$3@1$2$4&\2rd@1$1@1$0#5~b&\2op$h1~9&\2rl$8~9&\2aq$8~e&\2w0$c~f&\3csr@1$1@1$0#c@1$6@2$5$3@1$2$4&\2rm@1$1@1$0#3@1$6@2$5$3@1$2$4&\3rs1@1$1@1$0#5~h2&\2rd@1$1@1$0#5~h3&\3fmt$7~9\2ss$3\1w@1$2$4M8\0$8@1$9@2$5$3@1$2$4@1$h4@2$i5^2^1@1$6@2$5$3@1$2$4M9\1x@1$9$b@1$9@2$5$3@1$2$4@2$hf?2IT@1$h2^2\1i$bMb\1i$b@1$9@2$5$3@1$2$4^1~1~1\2rd@1$1@1$0#5\3imm@1$1@1$0#h5@1$6@2$5$3@1$2$4~4\1c$h8\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3imm@1$1@1$0#d@1$6@2$5$3@1$2$4\2sz$h0\6signed$8~4\2sz$h0~6\2op$a~4\2op$a\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#6@1$6@2$5$3@1$2$4~a~4\2op$a\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\5shamt@1$1@1$0#5@1$6@2$5$3@1$2$4~a\2fm@1$1@1$0#4\4pred@1$1@1$0#4\4succ@1$1@1$0#4~c~4@1$6@2$5$3@1$2$4@1$6@2$5$3@1$2$4~d~d\2w0$c\2aq$8\2rl$8~c~h0\2op$h7~h0\2op$e\2rd@1$1@1$0#5\3rs1@1$1@1$0#5~h1\2op$e\2rd@1$1@1$0#5\4uimm@1$1@1$0#5~h1\3fmt$7~4\3fmt$7~6\2op$hb\3fmt$7\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5\3rs3@1$1@1$0#5~h2\2op$h9\3fmt$7\2rd@1$1@1$0#5\3rs1@1$1@1$0#5\3rs2@1$1@1$0#5~h2\3fmt$7~h4\2op$hd~h5\2op$hc~h5\2op$ha~h5\3dst$f\3src$f~h4\3dir$d\3fmt$7\2rd@1$1@1$0#5\3rs1@1$1@1$0#5Md\3dir$d@1$9@2$5$3@1$2$4^4@1$6@2$5$3@1$2$4M7\3fmt$7@1$9@2$5$3@1$2$4^3@1$6@2$5$3@1$2$4@2$h3@2$5$3@1$2$4@4$h6$3@1$2$4@6$he@2$i6@1$h2^7+4@1$i2^7@1$h5$i4@1$i0^7@1$i1^7@1$6$i3^6\3fmt$7~c@1$6@2$5$3@1$2$4").

(* [comment removed for export] *)
Definition step1 : ltac2:(zQ "60!jb!hp6!hq3!hqa!hr3!h9>4ends@1$0$5>2ss$1>1w@1$0$2@1$3@2$4$1@1$0$2") := ltac2:(zQ "c0!jb!j4!im2!hp6!hq3!hqa!hr3!h9!hh7!ji7!jie!jjb\4ends@1$0$7\2ss$3\1w@1$0$4M1\0$1@1$5@2$6$3@1$0$4@2$8@1$2^2?7fmv_pcs@2$a^2^1@b$b?4segs?2IT?5x_cpy?5x_setZZZ?5BFUEL@2$9^3@1$2^2^2^1").

(* [comment removed for export] *)
Definition sp_below : ltac2:(zQ "30!hqa!h9!hp6>2ss$2@1$0$1") := ltac2:(zQ "h14!h9!jk6!hu3!jke!j4!ih6!hqa!il9!ima!jmb!jn2!ivb!hp6!jna!jo4!jod!jp3&\3op0$5\2a0$1\2b0$1@1$2$0&\3op0$7\2a0$1\2b0$1@1$2$0&\2sx$4\2lo$3\1n$3\1e$1@1$2$0&\2sx$4\1k$3\1i$0\1n$3@1$2$0\2ss$cM1\1x$1@1$6$0@4$9$1N2@1$b^1@1$aZ\1z$0@1$2$0\1n$3M3\1n$3@1$6$0^1@2$8$0Z\2n0$3@1$2$0\2op$5\1a$1\1b$1M5\2op$5@1$6$0^3M1\1a$1@1$6$0^2\1z$0@1$2$0\1n$3M3\1n$3@1$6$0^1M1\1b$1@1$6$0^2\1k$0@2$8$0M4\0$4$0@2$f$d^1@2$h0^1$e^1\2n0$3@1$2$0~0~0~1~1\2sx$4\2lo$3\2n0$3\1e$1@1$2$0\2sx$4\1k$3\1i$0\2n0$3@1$2$0\2n0$3@1$2$0~0~0~1~1~2~3@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0\2op$5\1a$1\1b$1@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$7\1a$1\1b$1@1$2$0~2~3").
Definition dead_below : ltac2:(zQ "30!j4!h9!jp9>1k$1>1K$2$0") := ltac2:(zQ "dd!jk6!jq3!jke!j4!h9!jg5!ih6!il9!jod!ji1!jqb!jp9!jr2&\2sx$3\2lo$2\1n$2\1e$0$1&\2sx$3\2k0$2\1i$4\1n$2$1&@2$a@2$8Z^1@2$8@2$9^3^1^8&\1n$4~2&M0\2n0$0$3^4~3\1n$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1&M2\2n1$2$3^1~4\1n$2$1&\2n1$2~5&M0\6a_base$0$3^2\1z$4$1~6\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1&\3off$4~7&\6a_base$0~8&M5\1a$5$3^2~9&\2n0$0~a&\1a$5~b\1k$4\1K$bMb\1K$b$3^1\1a$5\1w$2\1v$0M5\1a$5$3^3\6a_base$0\3off$4M0\6a_base$0$3^2\1z$4$1\1n$2M2\1n$2$3^1@2$8@2$9^2@1$c^5^8\2n0$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1~c\1a$5\1n$0\2k0$2$1\2lo$4\2hi$4$1\1e$0\1m$4$1\1e$0\2lo$4\2hi$4$1\1a$5\1n$0$1\2a1$5\2n1$0\2a2$5\2n2$0$1\1a$5\2n0$0\1c$4M5\1a$5$3^3\6a_base$0\3off$4M0\6a_base$0$3^2\1z$4$1\2n1$2M2\2n1$2$3^1M0\2n0$0$3^5\1n$4@2$a@2$8Z^1@2$8@2$9^3^1^9\1n$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1\1n$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1~c").
Definition prune : ltac2:(zQ "10!hp6>2ss$0$0") := ltac2:(zQ "h00!hqa!h9!jp9!hp6!hu3!in1!it1!iu7!jrb!iv1!im2!ivb!jg5!js4!jt1!jtc\2ss$3M0\1x@1$0$1$3@1$e^1\1k$1@6$6@1$a^2@1$b^2@1$8^2@3$f$2\1K$2@1$5@2$d^2^1@1$7^2@1$9^2@1$4$c^1").
Lemma prune_shape : ltac2:(zQ "h00!ju5!kg1!kg8!jp9!jb!iu7!jrb!iv1!im2!ivb!kge!jke!h9!jk6!jge!hp6>2ss$f@2$1@3$2$c@1$8@1$0^1@1$8^1@2$1@3$2@1$4$d@1$9@1$0^1@1$9^1@2$1@3$2$b@1$7@1$0^1@1$7^1@2$1@3$2@1$4$e@1$6@1$0^1@1$6^1>1K$3>0@3$a$3^1@1$5@1$0^2@3$a$3^2@1$5^3").
Proof.
  intros ss. unfold prune. destruct (sp_below ss); cbn [s_pc s_regs s_next s_log s_know]; repeat split; try reflexivity; auto.
  intros K HK. apply filter_In in HK. tauto.
Qed.
Lemma prune_INV : ltac2:(zQ "a0!hra!htd!kh3!jb!hqa!kjf!kk8!hp6!ju5!hq3>1E$6>2ss$7>1w@1$3$9>1R@2$5@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>0@6$2?4segs^5^4^3^2^1@6$2?4segs^6@1$8^5^4^3^2").
Proof.
  intros E ss w R M [HR HK]. ndestruct (prune_shape ss) as (Hpc & Hregs & Hnx & Hlog & Hsub).
  split; [rewrite Hregs; exact HR|].
  apply Forall_forall. intros K HKin. apply (proj1 (Forall_forall _ _) HK). apply Hsub. exact HKin.
Qed.

(* [comment removed for export] *)
Fixpoint seg_auto (fuel : nat) (first : bool) (ends : list Z) (ss : sym_state) (w : list went) : option (sym_state * list went) :=
  match fuel with
  | O => None
  | S f => if (negb first && inb (s_pc ss) ends)%bool then (if closed ss w then Some (ss, w) else None)
           else match step1 ends ss w with
                | Some (ss', w') =>
                    (* [comment removed for export] *)
                    if (Z.eqb (s_pc ss') (s_pc ss) && Nat.eqb (length w') (length w))%bool then None
                    else seg_auto f false ends (prune ss') w'
                | None => None
                end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)

Hypothesis IT_ok : ltac2:(zQ "10!lu1@2$0?4segs?2IT").
Hypothesis COPY : ltac2:(zQ "20!kpf!mj1>2fx$0@3$1^1?4segs?5x_cpy").
Hypothesis FILL : ltac2:(zQ "30!jo4!kpf!mje>2fx$1@4$2^1?4segs?5x_set$0").

Lemma pick_req : ltac2:(zQ "40!h9!jb!ji7!kkf>4ends@1$1$0>2pc$0@5$3?4segsZZZ@2$2^2^1").
Proof.
  intros ends pc. unfold pick.
  repeat (destruct (Z.eqb _ _) || destruct (inb _ _)); exact I.
Qed.

Lemma step_fmvdx_sound : ltac2:(zQ "hb0!hra!htd!jb!hp6!hq3!kg1!kla!kjf!kk8!iv1!kpf!hqa!hr3!kg8!im2!kqa!kr4!krc!kh3!ks7!kse!ima!ine!kud!lj3!lnd!jie>2fx$a>2ss$3>1w@1$2$4>3ss'$3>2w'@1$2$4>1E$8>1R@2$7@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$b@1$1@1$0#8>0@3$d@1$b@2$c$3@1$2$4@2$ha^7^6@2$h5@2$c$3@1$2$4@4$h6$3@1$2$4^5^4>0@6$h2?4segs^4^8^7^3^2@2$6$a\3fx'$a@2$6$8\2E'$8@2$6@2$7@1$0#5@1$1@1$0#k0\2R'@2$7@1$0#5@1$1@1$0#k0@2$5@3$d@1$1@1$0#i0@1$f^3@1$f^d@2$5@3$h8@1$9^c^8^2@2$5@2$h7@1$9^c@1$9^a@2$5@6$h2?4segs^2^a^9^1^6@3$h9?4segs@5$h0^d^7@2$h4@1$0#k0@1$e^c@4$h3?4segs^8^6^b@1$h1?4segs@5$h0^3^1@2$h4@1$0#k0@1$e^a@4$h3?4segs^2^6^9@1$h1?4segs").
Proof.
  intros fx ss w ss' w' E R M H HINV. unfold step_fmvdx in H.
  destruct (closed ss w) eqn:Hcl; [|discriminate]. cbn [negb] in H.
  destruct (itab_lookup IT (s_pc ss)) as [i|] eqn:Hl; [|discriminate].
  destruct i; try discriminate. destruct dir; try discriminate. destruct fmt; try discriminate.
  injection H as <- <-.
  destruct (SR.itab_fact segs IT IT_ok (s_pc ss) _ Hl) as (wd & Hf & Hec & Hd).
  destruct HINV as [HR HK].
  nexists (mkFP (bvmap_set rd (getr R rs1) (@fp_regs fx)) (@fp_csr fx)), E, R.
  split; [reflexivity|]. split; [apply XSegLib.APS.env_agree_refl|]. split; [cbn [s_next]; lia|].
  split; [split; [exact HR | exact HK]|].
  cbn [s_pc]. eapply mst_step; [reflexivity | exact (fp_step_fmv_d_x fx segs R (Z_to_bv 64 (s_pc ss)) (wden segs E M w) (seg_rom segs) wd rd rs1 Hf Hec Hd) |].
  replace (v_addi (Z_to_bv 64 (s_pc ss)) 4) with (Z_to_bv 64 (s_pc ss + 4)).
  2:{ unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. cbn [bv_modulus].
      change (2 ^ Z.of_N 64)%Z with (2 ^ 64)%Z. rewrite Zplus_mod_idemp_l. reflexivity. }
  apply mst_refl.
Qed.

Theorem seg_auto_sound : ltac2:(zQ "i00!hra!jb!htd!kg1!hp6!hq3!kg8!kla!kjf!kk8!iv1!kpf!j4!hqa!hr3!im2!kqa!kr4!krc!kh3!ks7!kse!ima!jke!ine!lo7!kud!h9!lj3!lnd!loe!jh8>2fx$b>4fuel$h7>5first$c>4ends@1$1$hb>2ss$4>1w@1$1$5>3ss'$4>2w'@1$1$5>1E$9>1R@2$8@1$0#5@1$2@1$0#k0>1M>0@1$2@1$0#k0@1$d@1$2@1$0#8>0@3$6@1$d@2$e$4@1$1$5@5$he^a^9^8^7^6@2$h6@2$e$4@1$1$5@4$h8$4@1$1$5^5^4>0@6$h3?4segs^4^8^7^3^2@2$7$b\3fx'$b@2$7$9\2E'$9@2$7@2$8@1$0#5@1$2@1$0#k0\2R'@2$8@1$0#5@1$2@1$0#k0@2$3@3$6@1$2@1$0#i0@1$h0^3@1$h0^h0@2$3@3$hc@1$a^c^8^2@2$3@2$ha@1$a^c@1$a^a@2$3@6$h3?4segs^2^a^9^1^6@2$3@3$6$c@2$hf^a^9$h9@3$hd?4segs@5$h1^h0^7@2$h5@1$0#k0@1$f^c@4$h4?4segs^8^6^b@1$h2?4segs@5$h1^3^1@2$h5@1$0#k0@1$f^a@4$h4?4segs^2^6^9@1$h2?4segs").
Proof.
  intros fx fuel. revert fx. induction fuel as [|f IH]; intros fx first ends ss w ss' w' E R M Hrun HINV; [discriminate|].
  cbn [seg_auto] in Hrun.
  destruct (negb first && inb (s_pc ss) ends)%bool.
  - destruct (closed ss w) eqn:Hc; [|discriminate]. injection Hrun as <- <-.
    nexists fx, E, R. split; [reflexivity|]. split; [apply XSegLib.APS.env_agree_refl|]. split; [lia|]. split; [exact HINV|]. split; [exact Hc|].
    apply mst_refl.
  - destruct (step1 ends ss w) as [[ss1 w1]|] eqn:Hs; [|discriminate].
    destruct (Z.eqb (s_pc ss1) (s_pc ss) && Nat.eqb (length w1) (length w))%bool; [discriminate|].
    unfold step1 in Hs.
    assert (STEP : exists (fx1 : FPState) E1 R1, @fp_csr fx1 = @fp_csr fx /\ env_agree (s_next ss) E E1 /\ (s_next ss <= s_next ss1)%nat
              /\ INV segs E1 ss1 w1 R1 M /\
              msteps segs (@mkst fx R (Z_to_bv 64 (s_pc ss)) (wden segs E M w) (seg_rom segs))
                          (@mkst fx1 R1 (Z_to_bv 64 (s_pc ss1)) (wden segs E1 M w1) (seg_rom segs))).
    { destruct (inb (s_pc ss) fmv_pcs).
      - exact (step_fmvdx_sound fx ss w ss1 w1 E R M Hs HINV).
      - exact (seg_step_sound segs IT x_cpy x_set 0 0 0 BFUEL IT_ok COPY FILL fx (pick ends (s_pc ss)) ss w ss1 w1 E R M
                  (pick_req ends (s_pc ss)) Hs HINV). }
    ndestruct STEP as (fx1 & E1 & R1 & Hfc1 & Hag1 & Hle1 & HINV1 & Hms1).
    ndestruct (prune_shape ss1) as (Ppc & Pregs & Pnx & Plog & Psub).
    destruct (IH fx1 false ends (prune ss1) w1 ss' w' E1 R1 M Hrun (prune_INV _ _ _ _ _ HINV1)) as (fx' & E' & R' & Hfc2 & Hag2 & Hle2 & HINV' & Hc' & Hms2).
    rewrite Pnx in Hag2, Hle2. rewrite Ppc in Hms2.
    nexists fx', E', R'. split; [rewrite Hfc2; exact Hfc1|]. split.
    { eapply XSegLib.APS.env_agree_trans; [exact Hag1|]. eapply XSegLib.APS.env_agree_le; [exact Hag2 | exact Hle1]. }
    split; [lia|]. split; [exact HINV'|]. split; [exact Hc'|].
    eapply msteps_trans; [exact Hms1 | exact Hms2].
Qed.
End WithSegs.
End SA2.
(* [comment removed for export] *)
