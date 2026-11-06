(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XHoare
  XFPSteps XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4boolhc4list36Stdlib5Lists4Listk27existsb46Stdlib6ZArith6BinInt1Zlf3eqb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~nd5sstephc3apphc4cons99OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XSegAuto2SA8WithSegs~~~~~~t23inbnd6SBlocknd5SCopynd5SFillnd7SFldSeqnd7SFsdSeq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~hkf9sym_statend4wenthc6optionhc4prodhkf4s_pct24picknd8seg_stephkf4exprhc4Nonehc3nat3h5LinuxProcessSemantics5Riscv5Instrhu75aluophu75mulophc4Some37Corelib5Lists7ListDefii43nthhkf4ELithkf6s_regshkf6two63zhkf5two64lf3leblf3subhkf6kentryhc5falsehkf5saddrlf3addhc4andblf6of_nathc4negbhkf3SSRhkf6s_knowhkf5s_loghkf6s_nextt2adead_belowt28sp_belowk26filtert25prune37Corelib4Init5Logiciv83andiv82eqk22Inhkf6sentry04Npos35stdpp9bitvectorbdefinitionsjie2bvnd3INV3h5LinuxProcessSemantics5Riscv7Preludejl75bvmaphkf3envnd8step_reqiv82ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~jpe7FPStatejpe6fp_csrjpe4mkstjpe7seg_romnd4wdenjie7Z_to_bvhc4pairhc4true37Corelib4Init5Peanoki52le79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHaXAxSymRun3~~~~~~kjf9env_agree79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~koc6mstepst28seg_autond6closed3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeku77Segmenthkf4itabhkfaitab_sound89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegLib4APSX~~~~~~ljd9copy_specljd9fill_spec" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import SR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module SA.
Section WithSegs.
Variable segs : ltac2:(zQ "20!jb!lhc@1$0$1").
Variable IT : ltac2:(zQ "10!li7$0").
Variables x_cpy x_set : Z.
Variable fsd_pcs fld_pcs : list Z.
Variable BFUEL : nat.

Definition inb : ltac2:(zQ "30!h9!j4!jb>1z$0>1l@1$2$0$1") := ltac2:(zQ "40!h9!jb!l5!n7\1z$0\1l@1$1$0@3$2$0@1$3^2^1").

Definition pick : ltac2:(zQ "30!h9!jb!rd>4ends@1$1$0>2pc$0$2") := ltac2:(zQ "d0!j4!h9!rd!s5!sb!hhc!n7!jb!hi2!hib!hj3!hjb!hk5\4ends@1$7$1\2pc$1M0\0$0$2@2$6^1?5x_cpy$9M0\0$0$2@2$6^1?5x_set$aM0\0$0$2@2$5^1?7fsd_pcs@1$cNi0M0\0$0$2@2$5^1?7fld_pcs@1$bNi0@1$8@3$4$1?5x_cpy@3$4$1?5x_set@3$3$1?7fsd_pcs@3$3$1?7fld_pcs^2").

(* [comment removed for export] *)
Definition step1 : ltac2:(zQ "60!jb!hp4!hq1!hq8!hr1!h9>4ends@1$0$5>2ss$1>1w@1$0$2@1$3@2$4$1@1$0$2") := ltac2:(zQ "70!jb!h9!hr8!hp4!hs0!hs7!hq1\4ends@1$0$1\2ss$3\1w@1$0$6@b$5?4segs?2IT?5x_cpy?5x_setZZZ?5BFUEL@2$4^3@1$2^2^2^1").

(* [comment removed for export] *)
Definition sp_below : ltac2:(zQ "30!hq8!h9!hp4>2ss$2@1$0$1") := ltac2:(zQ "h14!h9!ht2!hta!hu1!j4!igb!hq8!ih4!ihd!ijb!ik2!ika!hp4!il4!ile!im7!imd&\3op0$5\2a0$1\2b0$1@1$2$0&\3op0$7\2a0$1\2b0$1@1$2$0&\2sx$4\2lo$3\1n$3\1e$1@1$2$0&\2sx$4\1k$3\1i$0\1n$3@1$2$0\2ss$cM1\1x$1@1$6$0@4$9$1N2@1$b^1@1$aZ\1z$0@1$2$0\1n$3M3\1n$3@1$6$0^1@2$8$0Z\2n0$3@1$2$0\2op$5\1a$1\1b$1M5\2op$5@1$6$0^3M1\1a$1@1$6$0^2\1z$0@1$2$0\1n$3M3\1n$3@1$6$0^1M1\1b$1@1$6$0^2\1k$0@2$8$0M4\0$4$0@2$f$d^1@2$h0^1$e^1\2n0$3@1$2$0~0~0~1~1\2sx$4\2lo$3\2n0$3\1e$1@1$2$0\2sx$4\1k$3\1i$0\2n0$3@1$2$0\2n0$3@1$2$0~0~0~1~1~2~3@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0@1$2$0\2op$5\1a$1\1b$1@1$2$0\2op$7\1a$1\1b$1@1$2$0\2op$7\1a$1\1b$1@1$2$0~2~3").
Definition dead_below : ltac2:(zQ "30!j4!h9!in3>1k$1>1K$2$0") := ltac2:(zQ "dd!ht2!ind!hu1!j4!h9!io5!igb!ih4!im7!ioe!ip4!in3!ipb&\2sx$3\2lo$2\1n$2\1e$0$1&\2sx$3\2k0$2\1i$4\1n$2$1&@2$a@2$8Z^1@2$8@2$9^3^1^8&\1n$4~2&M0\2n0$0$3^4~3\1n$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1&M2\2n1$2$3^1~4\1n$2$1&\2n1$2~5&M0\6a_base$0$3^2\1z$4$1~6\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1&\3off$4~7&\6a_base$0~8&M5\1a$5$3^2~9&\2n0$0~a&\1a$5~b\1k$4\1K$bMb\1K$b$3^1\1a$5\1w$2\1v$0M5\1a$5$3^3\6a_base$0\3off$4M0\6a_base$0$3^2\1z$4$1\1n$2M2\1n$2$3^1@2$8@2$9^2@1$c^5^8\2n0$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1~c\1a$5\1n$0\2k0$2$1\2lo$4\2hi$4$1\1e$0\1m$4$1\1e$0\2lo$4\2hi$4$1\1a$5\1n$0$1\2a1$5\2n1$0\2a2$5\2n2$0$1\1a$5\2n0$0\1c$4M5\1a$5$3^3\6a_base$0\3off$4M0\6a_base$0$3^2\1z$4$1\2n1$2M2\2n1$2$3^1M0\2n0$0$3^5\1n$4@2$a@2$8Z^1@2$8@2$9^3^1^9\1n$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1\1n$2$1\2op$6\2a0$0\1b$0$1\2op$6\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1\2op$7\2a0$0\1b$0$1~0~1~c").
Definition prune : ltac2:(zQ "10!hp4>2ss$0$0") := ltac2:(zQ "h00!hq8!h9!in3!hp4!hta!iq4!iqb!ir2!irc!is5!hr8!ika!io5!isf!itc!iu7\2ss$3M0\1x@1$0$1$3@1$e^1\1k$1@6$6@1$a^2@1$b^2@1$8^2@3$f$2\1K$2@1$5@2$d^2^1@1$7^2@1$9^2@1$4$c^1").
Lemma prune_shape : ltac2:(zQ "h00!iv0!jgc!jh3!in3!jb!ir2!irc!is5!hr8!ika!jh9!hu1!h9!ht2!jhe!hp4>2ss$f@2$1@3$2$c@1$8@1$0^1@1$8^1@2$1@3$2@1$4$d@1$9@1$0^1@1$9^1@2$1@3$2$b@1$7@1$0^1@1$7^1@2$1@3$2@1$4$e@1$6@1$0^1@1$6^1>1K$3>0@3$a$3^1@1$5@1$0^2@3$a$3^2@1$5^3").
Proof.
  intros ss. unfold prune. destruct (sp_below ss); cbn [s_pc s_regs s_next s_log s_know]; repeat split; try reflexivity; auto.
  intros K HK. apply filter_In in HK. tauto.
Qed.
Lemma prune_INV : ltac2:(zQ "a0!ji8!jkb!jl1!jb!hq8!jnd!jo6!hp4!iv0!hq1>1E$6>2ss$7>1w@1$3$9>1R@2$5@1$0#5@1$1@1$0#k0>1M>0@1$1@1$0#k0@1$4@1$1@1$0#8>0@6$2?4segs^5^4^3^2^1@6$2?4segs^6@1$8^5^4^3^2").
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

Hypothesis IT_ok : ltac2:(zQ "10!lif@2$0?4segs?2IT").
Hypothesis COPY : ltac2:(zQ "20!jtd!lnf>2fx$0@3$1^1?4segs?5x_cpy").
Hypothesis FILL : ltac2:(zQ "30!ile!jtd!loc>2fx$1@4$2^1?4segs?5x_set$0").

Lemma pick_req : ltac2:(zQ "40!h9!jb!hs0!jod>4ends@1$1$0>2pc$0@5$3?4segsZZZ@2$2^2^1").
Proof.
  intros ends pc. unfold pick.
  repeat (destruct (Z.eqb _ _) || destruct (inb _ _)); exact I.
Qed.

Theorem seg_auto_sound : ltac2:(zQ "i00!ji8!jb!jkb!jgc!hp4!hq1!jh3!jp8!jnd!jo6!is5!jtd!j4!hq8!hr1!hr8!ju8!jv2!jva!jl1!kg5!kgc!ihd!hu1!kh7!khe!kj9!h9!knf!ks9!kt3!kte>2fx$b>4fuel$h7>5first$c>4ends@1$1$hb>2ss$4>1w@1$1$5>3ss'$4>2w'@1$1$5>1E$9>1R@2$8@1$0#5@1$2@1$0#k0>1M>0@1$2@1$0#k0@1$d@1$2@1$0#8>0@3$6@1$d@2$e$4@1$1$5@5$he^a^9^8^7^6@2$h6@2$e$4@1$1$5@4$h8$4@1$1$5^5^4>0@6$h3?4segs^4^8^7^3^2@2$7$b\3fx'$b@2$7$9\2E'$9@2$7@2$8@1$0#5@1$2@1$0#k0\2R'@2$8@1$0#5@1$2@1$0#k0@2$3@3$6@1$2@1$0#i0@1$h0^3@1$h0^h0@2$3@3$hc@1$a^c^8^2@2$3@2$ha@1$a^c@1$a^a@2$3@6$h3?4segs^2^a^9^1^6@2$3@3$6$c@2$hf^a^9$h9@3$hd?4segs@5$h1^h0^7@2$h5@1$0#k0@1$f^c@4$h4?4segs^8^6^b@1$h2?4segs@5$h1^3^1@2$h5@1$0#k0@1$f^a@4$h4?4segs^2^6^9@1$h2?4segs").
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
    npose (seg_step_sound segs IT x_cpy x_set 0 0 0 BFUEL IT_ok COPY FILL fx (pick ends (s_pc ss)) ss w ss1 w1 E R M
                  (pick_req ends (s_pc ss)) Hs HINV) as (fx1 & E1 & R1 & Hfc1 & Hag1 & Hle1 & HINV1 & Hms1).
    ndestruct (prune_shape ss1) as (Ppc & Pregs & Pnx & Plog & Psub).
    destruct (IH fx1 false ends (prune ss1) w1 ss' w' E1 R1 M Hrun (prune_INV _ _ _ _ _ HINV1)) as (fx' & E' & R' & Hfc2 & Hag2 & Hle2 & HINV' & Hc' & Hms2).
    rewrite Pnx in Hag2, Hle2. rewrite Ppc in Hms2.
    nexists fx', E', R'. split; [rewrite Hfc2; exact Hfc1|]. split.
    { eapply XSegLib.APS.env_agree_trans; [exact Hag1|]. eapply XSegLib.APS.env_agree_le; [exact Hag2 | exact Hle1]. }
    split; [lia|]. split; [exact HINV'|]. split; [exact Hc'|].
    eapply msteps_trans; [exact Hms1 | exact Hms2].
Qed.
End WithSegs.
End SA.
(* [comment removed for export] *)
