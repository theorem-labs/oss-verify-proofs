(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import AsanAllocModel.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset AllocWalkKit AW_DepotFrame AW_Leaves AW_InitCacheA AW_InitCacheB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import AllocTacX.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~k12wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~o15asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~s44cell46Stdlib6ZArith6BinInt1Zhg73add37Corelib4Init5Logichi63and01Zhg72le37Corelib4Init9Datatypeshka4conshka3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hn18rw_cellshf7Z_to_bvhka4Nonehi62eq3h5LinuxProcessSemantics5Riscv7Preludeht05bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AsdAW_InitCacheA~~~~~~hvfcic_trip_post79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AllocRep~~~~~~il25akobj79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsShadow~~~~~~ip95aceilip93mems42C4s42C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Exec~~~~~~iv13evt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~jj33mkR79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~jn62MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jr97mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jve7seg_romhg76modulohg73mulhg73subhka4listhka4prod89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2AscAW_InitCache4HCW2~~~~~~kn08icW_fromhka3nathka4pairjj36sub_fphg72lthg76of_natkn03icW3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticskv3dmachine_statehi62exhka6option69OSSVerify6Proofsaboost_jsonafuzz_parse3libeAsanAllocModel~~~~~~lkbaclass_sizelkb9max_countjj35munchjj35wmonokn0cic_loop_posthg76to_nat" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

End HCW.


Ltac deadK K := first [ exfalso; apply K; reflexivity
                      | exfalso; revert K; vm_compute; discriminate
                      | exfalso; revert K; rewrite ?unsigned_lit by lia; lia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma ic_trip : ltac2:(zQ "he0!h9!jc!nc!rc!hg0!hhf!hja!hk1!hk4!hm2!hma!hqc!hr8!hs2!hsa!hv6!ik2!ip0!it7!iu0!iu7!iuc!jic!jmf!jr3!jv3!kjd!kk8!kl2!kl9>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a2@1$1@1$0#k0>2a4@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t3@1$1@1$0#k0>2t4@1$1@1$0#k0>2t5@1$1@1$0#k0>2t6@1$1@1$0#k0>3mc0@1$1@1$0#k0>3cs0@1$1@1$0#k0>1F@2$f@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>1m$h3>1A$7>1c$7>0@2$h9$3^3>0@2$6@3$h1?5HCEIL^3+m0@2$6@2$8@2$5^3+m0@1$h2?5HCEIL@3$e$7@2$hb^3+8Z>0@4$b$3^5@2$5^4+4@3$9$4@1$h4^9@1$a$4>0@4$b$3^6@2$5^5+8@3$9$4@1$h5^9@1$a$4>0@2$6@2$8+1^5@2$8^5+hf@3$h6$3@he$h0^i3^i2^i1^i0@1$2+h0@1$2+h1@1$2+ig0^hf^he^hd^hc^hb@1$2+f@1$2+kg0^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^d^a^9^8^7^6@7$h8@hf$h7^i3^i2^i1^i0@1$2+h0@1$2+h1@1$2+ig0^hf^he^hd@1$2@2$5^7+8^hc@1$2@2$hc+i0^6^hb@2$c@1$0#k0@2$hd^6+h0@1$2+f@1$2+kg0^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^a@2$c@1$0#k0+mtvt8^9@1$d@1$1@1$0#k0^8@1$ha$3").
Proof.
  intros. destruct (Z.le_gt_cases c 16).
  - eapply ic_trip_lo; eauto. lia.
  - eapply ic_trip_hi; eauto. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint icW_from (CA : Z) (c : Z) (k : nat) : list (Z * Z) :=
  match k with O => [] | S k' => (CA + 80 * c + 4, CA + 80 * c + 16) :: icW_from CA (c + 1) k' end.
(* [comment removed for export] *)
Definition icW : ltac2:(zQ "30!hk1!km0!km8>2CA$0@1$1@2$2$0$0") := ltac2:(zQ "20!hk1!kr7\2CA$0@3$1^1+1Nhf").

(* [comment removed for export] *)
Lemma icW_from_sub : ltac2:(zQ "e0!hk1!hhf!km8!kl2!hm2!ks3!hma!ksa!hja!kr7!kt2!hk4!ktc!ku2>2CA$0>1k$5>2c0$0>1c$0>0@2$8@2$b^2^1@2$c^1@2$1^2@1$d^3@2$a@3$4@2$2$0$0@4$7$0$0@2$1@2$1^5@2$3+l0^2+4@2$1@2$1^5@2$3+l0^2+h0@1$6@2$2$0$0@3$9^5^3^4").
Proof.
  intros CA k. induction k as [|k IH]; intros c0 c Hc x OUT; [exfalso; clear - Hc; lia|].
  cbn [icW_from outside] in OUT. destruct OUT as [O1 O2].
  destruct (Z.eq_dec c c0) as [->|NE].
  - cbn [outside]. split; [exact O1| exact I].
  - apply (IH (c0 + 1) c); [clear - Hc NE; lia| exact O2].
Qed.
Lemma icW_sub : ltac2:(zQ "b0!hk1!hhf!km8!hk4!kl2!hm2!hma!ksa!hja!kuc!kt2>2CA$0>1c$0>0@2$8@2$3+1^1@2$3^1+hf@2$a@3$5@2$2$0$0@4$7$0$0@2$1@2$1^3@2$4+l0^2+4@2$1@2$1^3@2$4+l0^2+h0@1$6@2$2$0$0@1$9^3").
Proof. intros CA c Hc. unfold icW. apply icW_from_sub. clear - Hc. cbn. lia. Qed.

Definition ic_loop_post : ltac2:(zQ "60!h9!jc!hk1!lia!hv6!iu0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2t0@1$1@1$0#k0>2t1@1$1@1$0#k0>2t2@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2a0@1$1@1$0#k0>2a2@1$1@1$0#k0>2a4@1$1@1$0#k0>2a6@1$1@1$0#k0>2a7@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>2t6@1$1@1$0#k0>1F@2$4@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2m0$5>2CA$2>0$3P") := ltac2:(zQ "i01!h9!jc!hja!hhf!rc!ljb!hg0!nc!kl2!hm2!hma!lk1!hk1!lia!hqc!hk4!hr8!hs2!hsa!hv6!kuc!iu0!loc!lpa!iu7!iuc!jmf!lq7!lr0!jr3!jv3!kjd&>0@1$1@1$0#k0@1$b@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2t0@1$1@1$0#k0\2t1@1$1@1$0#k0\2t2@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2a0@1$1@1$0#k0\2a2@1$1@1$0#k0\2a4@1$1@1$0#k0\2a6@1$1@1$0#k0\2a7@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\2t6@1$1@1$0#k0\1F@2$h3@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2m0$h5\2CA$c\3ms'$d@2$5@1$1@1$0#k0\2t3@1$1@1$0#k0@2$5@1$1@1$0#k0\2t4@1$1@1$0#k0@2$5@1$1@1$0#k0\2t5@1$1@1$0#k0@2$5~0\2m'~0@2$2@3$h2$d^5@7$hd@hf$ha^i2^i1^i0^hf^he^hd^hc^hb^ha^h9@1$7@2$3@2$3^6@2$8+l0+i0+8^h8@1$7@2$8+i0+i0^h7@2$h0@1$0#k0+h0^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^4^3^2^a^9@2$h0@1$0#k0+mugic^8@1$h1@1$1@1$0#k0^1@1$hf$4@2$2@3$hb@1$h4^6^7^1@2$2@3$hc$4^7^1@2$2@2$he$4^1>2c'$c>0@2$2@2$f+1^1@2$f^1+hf@2$2@4$e$4^3@2$3@2$3^8@2$8+l0^2+4@3$9$6@1$h8@1$7@1$h7^2@1$a$6@4$e$4^3@2$3@2$3^8@2$8+l0^2+8@3$9$6@1$h9@1$7@1$h6^2@1$a$6").

Section Loop.
  Variables (ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem).
  Variable CA : Z.
  Hypothesis CAR : ltac2:(zQ "80!hja!hsa!hk1!ip0!it7!hhf!hk4!kk8@2$0@3$3?5HCEIL?2CA+qi0@2$0@2$6@2$5?2CA+qi0@1$4?5HCEIL@3$1$2@2$7?2CA+h0Z").

  Let CAE : 4096 <= CA /\ CA + 2592 <= aceil. Proof. exact (akobj_env _ _ (proj1 CAR) ltac:(clear; lia)). Qed.   (* [comment removed for export] *)
  Lemma ic_loop : ltac2:(zQ "i30!nc!h9!hhf!rc!hg0!jc!kl2!hja!hk4!hm2!hma!hqc!hk1!ks3!ljb!iu7!iuc!kl9!hr8!hs2!hsa!kuc!lr9!iu0!loc!lpa!jic!jmf!lq7!lr0!jr3!jv3!kjd!ktc!ls9>1k$d>1c$c>2t3@1$5@1$1#k0>2t4@1$5@1$1#k0>2t5@1$5@1$1#k0>1m$h7>0@3$h4$d@1$i2@2$h1+i0^5^6>0@2$7@2$8+1^6@2$8^6+hf>0@2$hf$3^3>0@3$hc@1$h5?2CA?2m0^4>0@3$hd$3?2m0^5>0>2c'$c>0@2$7@2$8+1^1@2$i1^1^b@2$7@4$b$3^8@2$2@2$2?2CA@2$6+l0^2+4@3$9$4@1$f@1$0@1$h9^2@1$a$4@4$b$3^8@2$2@2$2?2CA@2$6+l0^2+8@3$9$4@1$h0@1$0@1$h8^2@1$a$4>0>2c'$c>0@2$7@2$8^c^1@2$8^1+hf@2$e@1$5@1$1#k0\2mc@1$5@1$1#k0@2$e@1$5@1$1#k0\2cs@1$5@1$1#k0@2$7@4$b$3^b@2$2@2$2?2CA@2$6+l0^4+4@3$9$4@1$f^2@1$a$4@4$b$3^b@2$2@2$2?2CA@2$6+l0^4+8@3$9$4@1$h0^1@1$a$4@3$ha$3@hd$h6?2ra?2sp?2gp?2tp@1$0+h0@1$0+h1@1$0+ig0?2s0?2s1?2a0?2a2?2a4@1$0+f@1$0+kg0?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11?2t6?1F?2fc?2m0?2CA@7$he@hf$hb?2ra?2sp?2gp?2tp@1$0+h0@1$0+h1@1$0+ig0?2s0?2s1?2a0@1$0@2$2@2$2?2CA@2$6+l0^c+8?2a2@1$0@2$6+i0^c?2a4@2$h2@1$1#k0@2$h1^c+h0@1$0+f@1$0+kg0?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^b^a^9?2t6?1F@2$h2@1$1#k0+mtvt8?2fc@1$h3@1$5@1$1#k0^8@1$i0$3").
  Proof.
    unfold AHI_LO in CAR. acb.
    induction k as [|k IH]; intros c t3 t4 t5 m HK Hc MI MU WM DONE CELLS. { exfalso. clear - HK Hc; try acb. lia. }
    ndestruct (CELLS c ltac:(hci; clear - Hc; try acb; lia)) as (mc & cs & MC & CS).
    replace (CA + 80 * c + 8) with (CA + 80 * c + 0 + 8) by (clear; lia).
    replace (CA + 80 * c + 4) with (CA + 80 * c + 0 + 4) in MC by (clear; lia).
    replace (CA + 80 * c + 8) with (CA + 80 * c + 0 + 8) in CS by (clear; lia).
    eapply evt_cut.
    { eapply (ic_trip ra sp gp tp s0 s1 a0 a2 a4 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 mc cs F fc m (CA + 80 * c + 0) c MI); [| exact MC | exact CS | exact Hc].
      unfold AHI_LO. acb. clear - CAR Hc; try acb. Z.div_mod_to_equations. aunf; lia. }
    intros ms' POST. ndestruct POST as (t3' & t4' & t5' & m' & -> & MU1 & WM1 & MI1 & MC1 & CS1).
    replace (CA + 80 * c + 0 + 88) with (CA + 80 * (c + 1) + 8) by (clear; lia).
    replace (CA + 80 * c + 0 + 4) with (CA + 80 * c + 4) in * by (clear; lia).
    replace (CA + 80 * c + 0 + 8) with (CA + 80 * c + 8) in * by (clear; lia).
    replace (CA + 80 * c + 0 + 16) with (CA + 80 * c + 16) in * by (clear; lia).
    replace (32 * c + 32) with (32 * (c + 1)) by (clear; lia).
    assert (MU' : munch (icW CA) m0 m').
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [apply icW_sub; exact Hc| exact MU1]. }
    assert (WM' : wmono asegs m0 m') by (eapply wmono_trans; [exact WM| exact WM1]).
    assert (DONE' : forall c', 1 <= c' < c + 1 -> rw_cells asegs m' (CA + 80 * c' + 4) [C4 (wz (max_count c'))] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 (wz (class_size c'))]).
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [split; [exact MC1| exact CS1]|].
      destruct (DONE c' ltac:(hci; clear - Hc' NE; try acb; lia)) as [D1 D2]. split.
      - eapply rw_cells_transport; [exact D1| exact MU1| exact WM1|]. cbn. clear - Hc' NE; try acb. lia.
      - eapply rw_cells_transport; [exact D2| exact MU1| exact WM1|]. cbn. clear - Hc' NE; try acb. lia. }
    assert (CELLS' : forall c', c + 1 <= c' <= 31 -> exists mc cs, rw_cells asegs m' (CA + 80 * c' + 4) [C4 mc] /\ rw_cells asegs m' (CA + 80 * c' + 8) [C8 cs]).
    { intros c' Hc'. ndestruct (CELLS c' ltac:(hci; clear - Hc' Hc; try acb; lia)) as (mc' & cs' & D1 & D2). exists mc', cs'. split.
      - eapply rw_cells_transport; [exact D1| exact MU1| exact WM1|]. cbn. clear - Hc'; try acb. lia.
      - eapply rw_cells_transport; [exact D2| exact MU1| exact WM1|]. cbn. clear - Hc'; try acb. lia. }
    clear MC CS MC1 CS1 MU1 WM1 DONE CELLS MU WM MI.
    destruct (Z.eqb_spec c 31) as [E31|N31].
    - (* [comment removed for export] *)
      rewrite E31. apply evt_done. unfold ic_loop_post. nexists t3', t4', t5', m'.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI1|].
      intros c' Hc'. apply DONE'. clear - Hc' E31; try acb. lia.
    - replace (c - 15) with ((c + 1) - 16) by (clear; lia).
      eapply (IH (c + 1)); try eassumption. { clear - HK Hc N31; try acb. lia. } { clear - Hc N31; try acb. lia. }
  Qed.
End Loop.

End HCW2.

(* [comment removed for export] *)
