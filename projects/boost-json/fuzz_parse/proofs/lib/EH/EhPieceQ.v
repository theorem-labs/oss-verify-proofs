(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require EH0Gc1. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.EH Require Import XPropExec XCatExec XCatSim XSeqExec XStoreOk XSymExec
  XAxSymExec3 XAxSymExec3B XAxSymExec3Sound XAxSymRun3 XAsanPlanCore XAsanPlan XSegLib XLibSym XSegRun XSegAuto
  EhX_plain EhCut EhMatch EhPiece EhPieceP.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04list03nat04prod89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHbXAxSymExec33AX2~~~~~~i94expr04bool46Stdlib5Arith8PeanoNat3Natnb3eqb36Stdlib5Lists4Listpc7existsb89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhMatch5MATCH~~~~~~r95subst89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceQ6PIECEQ~~~~~~hg45shape89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XSegRun2SR~~~~~~hl26region37Corelib7Numbers7BinNumshpc1Z05falsepc7forallb04andb03fst3h5LinuxProcessSemantics5Riscv5Instrht65aluopht65mulophg43inb04negb03snd04true89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8EhPieceP6PIECEP~~~~~~ii45bindsi96kentryi99sym_statehpc4Npos35stdpp9bitvectorbdefinitionsiof2bv37Corelib4Init5Logicir23andir22eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9EhX_plain~~~~~~it34SEGS06optionir22ex3h5LinuxProcessSemantics5Riscv7Preludeji85bvmapi93envi92ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH9XPropExec~~~~~~jm27FPStatei92ebi96s_nextjm26fp_csrjm24mkstjm27seg_romiof7Z_to_bv03nil04pair37Corelib4Init5Peanojud2lt89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHdXAsanPlanCore3APC~~~~~~kg7cexpr_vars_lti96edenoti94s_pc89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EHh0XAxSymExec3Sound4AX2S~~~~~~kme7know_okkme7regs_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7XCatSim~~~~~~kt06mstepshl23INVhl27outsidehl2aregions_okhl24went79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH8XStoreOk~~~~~~ljf9mem_growspc2In04Somer96sg_get04None89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH7EhPiece5PIECE~~~~~~lq45pc_pvlq4apc_regionslq48pc_entrylq45pc_sglq46pc_xknlq46pc_xpclq48pc_xregslq45piecelq48piece_okhg49Pgen_spechg4bshape_holdsit39COPY_SPECit39FILL_SPEClq4bpiece_checki98expr_eqbr96esubst04consr95unifyhg46dom_inr9aunify_regsr9abind_cellsr9crematch_fromlq46set_sg37Corelib4Init3Natmuc3add37Corelib5Lists7ListDefng53nthii48CS_SLOTS89OSSVerify6Proofsaboost_jsonafuzz_parse3lib2EH5EhCut3CUT~~~~~~nif4sitei94EVarhg48slot_varng53mapng53seqht67ALU_ADDnif7s_fsizeii4bsaved_counti94EAlui94ELitnb3ltb03appmuc3sub46Stdlib6ZArith6BinInt1Zntc3addii48shape_okhg4astep_shapenif7CUT1_PCnif2PVnif4cut1nif6cut1_Tnif9cut1_regsii4acont_pieceii47regions" s.   (* [comment removed for export] *)
Import ListNotations. Import AX2. Import AX2S. Import SR. Import SA. Import CUT. Import MATCH. Import PIECE. Import PIECEP.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PIECEQ.

Definition shape : ltac2:(zQ "00S") := ltac2:(zQ "40!h8!he!i3!me@1$0@2$2$1$3").

Definition inb : ltac2:(zQ "30!he!n5!h8>1n$0>1l@1$2$0$1") := ltac2:(zQ "40!he!h8!p6!qf\1n$0\1l@1$1$0@3$3$0@1$2^2^1").

(* [comment removed for export] *)
Definition shape_holds : ltac2:(zQ "60!h8!n5!he!vc!hk9!hp2>2pv@1$0$2>2rg@1$0$5>2sh$4>2sg$3$1") := ltac2:(zQ "h40!me!i3!he!hr5!hra!n5!hs1!hsb!ht1!h8!hva!ig3!igc!ih3!ih9!ihe!vc!im9!hk9!hp2\2pv@1$9$2\2rg@1$9$h3\2sh$h2\2sg$h0@2$7@2$7@3$6@2$1$2$0\2ne@2$1$2$0@3$h1^2@3$8$2$0^1@3$e$2$0^1^2@3$6@2$1$2$0\2ne@2$1$2$0@2$c@3$8$2$0^1^5^1@3$6@2$1@2$1$0$3$3\1r@2$1@2$1$0$3$3M1\1r@2$1@2$1$0$3$3$5^1\1y@2$1$0$3\2y0$3M1\1y@2$1$0$3$5^2\2y1$0\2y2$3M0\2y1$0$5^2\1z$3$f\1n$2@1$d@2$c^1^a\2op$a\1a$0\1b$0$4\2op$a\1a$0\1b$0$4\2op$b\1a$0\1b$0$4\2op$b\1a$0\1b$0$4\2sx$5\2lo$2\1n$2\1e$0$4\2sx$5\1k$2\1i$3\1n$2$4^3").

Definition Pgen_spec : ltac2:(zQ "80!h8!he!hr5!hk9!me!in2!inb!hp2>5entry$6>3xpc$2>5xregs@1$0$4>3xkn@1$0$5>2rg@1$0$7>2pv@1$0$1>2sh$3P") := ltac2:(zQ "id1!io7!iqc!is6!isd!he!h8!jh2!jha!ji2!me!jke!jl7!jld!jq1!n5!jqc!jr1!jra!js4!jsc!jt7!hra!ju2!ju7!i3!ihe!kg1!hr5!igc!hk9!kke!kle!in2!km7!inb!kra!ks5!lgd!lh7!lhe!hp2!li9!lj7!lnd!loa&>0@1$1@1$0#k0@1$7@1$1@1$0#8\5entry$i2\3xpc$hb\5xregs@1$5$9\3xkn@1$5$i0\2rg@1$5$i8\2pv@1$5$4\2sh$hd>2fx$d>1E$b>1R@2$a@1$0#5@1$1@1$0#k0>1M~0>0@6$i6$6^3^b@1$h6$ia^2^1@2$8$d\3fx'$d@2$8$b\2E'$b@2$8@2$a@1$0#5@1$1@1$0#k0\2R'@2$a@1$0#5@1$1@1$0#k0@2$8~0\2M'~0@2$2@3$i5$6@5$h2^9^7@2$h4@1$0#k0@1$i1^h0^6@1$h3$6@5$h2^4^2@2$h4@1$0#k0^f^1@1$h3$6@2$2@3$i4^3^e^2@2$2@4$i3$6^3^1^d@2$2>1n$4>1e$9>0@3$ic@2$h8$4$9@4$h7$4$9^2^1^c>0@3$3$e@2$he@1$h0^h3^2$h9@3$3@1$1@1$0#k0@2$c^7^4@2$hf^c^3@2$2>1n$4>0@2$ha^1@1$h0^h1>0@3$3$e@2$hc^2^d$h5@3$3@1$1@1$0#k0@2$c^6^3@2$c^b^3@2$2@3$3>0$4@1$5@1$1@1$0#8@1$f^3@1$f^8@2$2@2$i9^3^c@2$2>1a@1$1@1$0#k0>0@3$i7^4^d^1@3$3@1$7@1$1@1$0#8@1^3^2@1^8^2@2$2@2$ib^6^1@3$3@1$1@1$0#i0@1$h1^4@1$h1^9").

Lemma sg_get_in : ltac2:(zQ "b0!me!he!lof!jha!ju7!i3!isd!ji2!lp5!vc!loa>2sg$9>1n$1>1e$0>0@3$6@1$3$0@2$8^3^2@2$2$0^1@2$7$0\2e'$0@3$a@2$5$1$0@4$4$1$0^4^1^5").
Proof.
  intros sg n e. induction sg as [|[m e0] r IH]; cbn [sg_get]; [discriminate|].
  destruct (Nat.eqb m n) eqn:Hm.
  - intros _. apply Nat.eqb_eq in Hm. subst m. exists e0. left. reflexivity.
  - intros H. destruct (IH H) as [e' He']. exists e'. right. exact He'.
Qed.

Lemma dom_free : ltac2:(zQ "e0!he!me!i3!isd!n5!h8!igc!lpe!hra!ht1!jha!ihe!lp5!hs1>2pv@1$5$0>2sg@1$5@2$2$0$1>1n$0>0@3$3$4@3$d@2$2$0$1\2ne@2$2$0$1@2$6@3$9$0$1^1^4^2$b>0@3$3$4@2$6^2^4$8@3$3@1$a$1@2$c^4^3@1$7$1").
Proof.
  intros pv sg n Hd Hn. destruct (sg_get sg n) as [e|] eqn:Hg; [|reflexivity].
  destruct (sg_get_in _ _ _ Hg) as [e' Hin]. rewrite forallb_forall in Hd. specialize (Hd _ Hin). cbn [fst] in Hd.
  rewrite Hd in Hn. discriminate.
Qed.

Theorem Pgen_of_piece : ltac2:(zQ "h10!n5!ihe!isd!lu7!lv0!lve!mga!mh3!mhd!mi7!mj3!mjc!mk8!hk9!ml5!mm4!mn1>0$f>0$h0>1p$a>2sh$d>0@3$2$0@1$b^2$1>0@3$2$0@4$e@1$3^3@1$4^3^2@1$6^3$1@7$c@1$5^4@1$8^4@1$9^4@1$7^4@1$4^4@1$3^4^3").
Proof.
  intros COPY FILL p sh Hok Hsh fx E R M HINV.
  ndestruct (piece_sound COPY FILL p fx E R M Hok HINV) as (fx' & E' & R' & M' & Hag & Hms & HR & HK & ROK & Hout & Hgr & Hfc).
  unfold shape_holds in Hsh. apply andb_true_iff in Hsh as [Hsh Hrg]. apply andb_true_iff in Hsh as [Hsh Hdom].
  assert (FREE : forall n, inb n (pc_pv p) = false -> ev (Es E' (pc_sg p)) n = ev E' n).
  { intros n Hn. apply Es_free. eapply dom_free; eauto. }
  exists fx', (Es E' (pc_sg p)), R', M'.
  split; [exact Hms|]. split; [exact HR|]. split; [exact HK|].
  split.
  { intros n e Hin Hvars. rewrite forallb_forall in Hsh. specialize (Hsh _ Hin). cbn [fst snd] in Hsh.
    rewrite (binds_sound E' (pc_sg p) n e Hsh). symmetry. apply (edenot_agree_AP (s_next (pc_entry p))); [exact Hag | exact Hvars]. }
  split.
  { intros n Hn Hfree. rewrite (FREE n Hfree). symmetry. apply (proj1 Hag). exact Hn. }
  split; [cbn [Es eb]; symmetry; apply (proj2 Hag)|].
  assert (BASES : forall rb rlo rlen, In (rb, rlo, rlen) (pc_regions p) ->
            estart (Es E' (pc_sg p)) (SA rb rlo) = estart E' (SA rb rlo)).
  { intros rb rlo rlen Hr. rewrite forallb_forall in Hrg. specialize (Hrg _ Hr). cbn beta iota in Hrg.
    unfold estart. cbn [a_base a_off].
    destruct rb as [z|n| | | | | |]; try discriminate; [reflexivity|].
    cbn [edenot]. rewrite FREE; [reflexivity|]. destruct (inb n (pc_pv p)); [discriminate | reflexivity]. }
  split.
  { unfold regions_ok in *. apply Forall_forall. intros [[rb rlo] rlen] Hr.
    pose proof (proj1 (Forall_forall _ _) ROK _ Hr) as X. cbn beta in X. rewrite (BASES _ _ _ Hr). exact X. }
  split.
  { intros a Ha. apply Hout. unfold outside in *. apply Forall_forall. intros [[rb rlo] rlen] Hr.
    pose proof (proj1 (Forall_forall _ _) Ha _ Hr) as X. cbn beta in X. rewrite <- (BASES _ _ _ Hr). exact X. }
  split; [exact Hgr | exact Hfc].
Qed.

Theorem Pgen_of_check : ltac2:(zQ "h00!lu7!lv0!n5!ihe!isd!lve!mh3!mhd!mi7!mj3!mne!mk8!hk9!ml5!mm4!mn1>0$e>0$f>1p$9>2sh$c>0@3$4$2@2$a^2@3$d@1$0^2@1$1^2^1$3@7$b@1$5^3@1$7^3@1$8^3@1$6^3@1$1^3@1$0^3^2").
Proof.
  intros COPY FILL p sh H.
  destruct (piece_check_sound _ _ H) as (sg & Hok & Hsh).
  exact (Pgen_of_piece COPY FILL (set_sg p sg) sh Hok Hsh).
Qed.

(* [comment removed for export] *)
Definition dom_in : ltac2:(zQ "30!h8!he!vc>2pv@1$0$1>2sg$2P") := ltac2:(zQ "b0!he!me!n5!h8!ju7!i3!ihe!isd!vc!igc!loa\2pv@1$3$0\2sg$8>1n$0>1e$1>0@3$a@2$5$0$1@4$4$0$1^2^1^3@3$7$2@2$9^3^5$6").

(* [comment removed for export] *)
Lemma unify_unfold : ltac2:(zQ "h56!vc!n5!me!jha!he!lpe!lof!mod!mp8!h8!i3!hr5!hva!ig3!mq1!ju7!isd!lp5!mq7!p6!qf&M1\0$1@1$3$0@2$7@2$8^5^7^6@2$6$0^5@1$5$0&\1b$2~0&\1a$2~1&\2op$c~2&\2op$d~2&M1\0$1@1$3$0@2$7@2$8^6^8^7@2$6$0^6@1$5$0>2pv@1$9$4>4fuel$4>1t$2>1x$2>2sg$0@3$h0@1$3$0@5$h2^5^4^3^2^1M4\4fuel$4@1$3$0^4@1$5$0\1n$4M2\1t$2@1$3$0^4\1z$bM1\0$1@1$3$0@2$7@2$8^3^5^4@2$6$0^3@1$5$0\1n$4M1\0$1@1$3$0@3$h4$4@1$h3^1^7M3\1x@1$3$2@1$3$0@2$h1^3^1\1e$2M1\0$1@1$3$0@2$7^1^5@2$6$0^4@1$5$0@2$6@1$9@2$a$4$2@3$e@2$a$4$2@4$f$4$2^1^4^3M1\0$1@1$3$0@2$7^5^4@2$6$0^3@1$5$0~3~3~4~4\2sx$1\2lo$4\1n$4\1e$2~5\2sx$1\1k$4\1i$b\1n$4~5").
Proof. intros pv; destruct pv; reflexivity. Qed.

Lemma unify_dom : ltac2:(zQ "90!vc!he!mqf!me!lof!h8!jha!isd!mq7>2pv@1$5$1>4fuel$1>1t$3>1x$3>2sg$0>3sg'$0>0@3$7@1$6$0@5$8^6^5^4^3^2@2$4$0^1>0@2$2^7^3@2$2^8^3").
Proof.
  intros pv fuel. induction fuel as [|fuel IH]; intros t x sg sg' H Hd; rewrite unify_unfold in H; [discriminate|].
  assert (GEN : forall bb : bool, (if bb then Some sg else None) = Some sg' -> dom_in pv sg').
  { intros [|] Hb; [injection Hb as <-; exact Hd | discriminate]. }
  destruct t as [z|n| | | | | |]; try (eapply GEN; exact H).
  unfold inb in *. destruct (existsb (Nat.eqb n) pv) eqn:Hn; [|eapply GEN; exact H].
  destruct (sg_get sg n) as [e|]; [eapply GEN; exact H|].
  injection H as <-. intros m e' [Hin|Hin]; [injection Hin as <- <-; exact Hn | exact (Hd m e' Hin)].
Qed.

Lemma unify_regs_dom : ltac2:(zQ "90!vc!h8!mqf!me!lof!he!jha!isd!mr9>2pv@1$1$5>3srT@1$1$3>3srX@1$1$3>2sg$0>3sg'$0>0@3$7@1$6$0@4$8^5^4^3^2@2$4$0^1>0@2$2^6^3@2$2^7^3").
Proof.
  intros pv srT. induction srT as [|t rT IH]; intros srX sg sg' H Hd; destruct srX as [|x rX]; cbn [MATCH.unify_regs] in H; try discriminate.
  - injection H as <-. exact Hd.
  - destruct (unify pv 2 t x sg) as [sg1|] eqn:Hu; [|discriminate].
    eapply IH; [exact H|]. eapply unify_dom; eauto.
Qed.

Lemma bind_cells_dom : ltac2:(zQ "90!vc!h8!mqf!in2!lof!he!jha!isd!ms6>2pv@1$1$5>1T@1$1$3>1X@1$1$3>2sg$0>3sg'$0>0@3$7@1$6$0@4$8^5^4^3^2@2$4$0^1>0@2$2^6^3@2$2^7^3").
Proof.
  intros pv T. induction T as [|K r IH]; intros X sg sg' H Hd; cbn [MATCH.bind_cells] in H.
  - injection H as <-. exact Hd.
  - destruct K; try (eapply IH; [exact H | exact Hd]).
    destruct (find_word X (asubst sg a) w) as [x|]; [|eapply IH; [exact H | exact Hd]].
    destruct (unify pv 2 v x sg) as [sg1|] eqn:Hu; (eapply IH; [exact H|]); [eapply unify_dom; eauto | exact Hd].
Qed.

Lemma rematch_from_dom : ltac2:(zQ "a0!h8!vc!mqf!me!in2!lof!he!jha!isd!mt3>3sg0$1>2pv@1$0$6>3srT@1$0$3>1T@1$0$4>3srX@1$0$3>1X@1$0$4>2sg$1>0@3$8@1$7$1@6$9^7^6^5^4^3^2@2$5$1^1>0@2$2^7^8@2$2^8^3").
Proof.
  intros sg0 pv srT T srX X sg H Hd. unfold rematch_from in H.
  destruct (unify_regs pv srT srX sg0) as [sg1|] eqn:H1; [|discriminate].
  destruct (bind_cells pv T X sg1) as [sg2|] eqn:H2; [|discriminate].
  destruct (all_present T X sg2); [|discriminate]. injection H as <-.
  eapply bind_cells_dom; [exact H2|]. eapply unify_regs_dom; [exact H1 | exact Hd].
Qed.

Lemma dom_in_forallb : ltac2:(zQ "c0!he!me!i3!n5!ht1!h8!ihe!isd!vc!mqf!igc!hs1>2pv@1$5$0>2sg$8>0@2$9^2^1@3$7$3@3$b@2$2$0$1\2ne@2$2$0$1@2$a@3$4$0$1^1^4^2$6").
Proof.
  intros pv sg Hd. apply forallb_forall. intros [n e] Hin. cbn [fst]. exact (Hd n e Hin).
Qed.

Lemma piece_check_sound_dom : ltac2:(zQ "d0!n5!ihe!isd!vc!is6!lu7!mqf!ji2!mga!mj3!mne!mjc!mu2>1p$9>5extra>0$3$0>0@3$2$0@2$a^2^1$1>0@2$6@1$5^3@1$8^3@2$7$3\2sg$3@2$4@3$2$0@1$b@2$c^5^1$1@2$4@3$2$0@1^4^1$1@2$6@1$5^5^1").
Proof.
  intros p extra H Hd0. unfold piece_check in H. unfold piece_ok.
  destruct (pc_k p) as [|k] eqn:Hk; [discriminate|]. cbn [set_sg pc_k pc_fuel pc_ends pc_entry]. rewrite Hk.
  destruct (EhX_plain.run_k (S k) (pc_fuel p) (pc_ends p) (pc_entry p) []) as [[ssX wX]|]; [|discriminate].
  destruct (rematch_from (pc_sg p) (pc_pv p) (pc_xregs p) (pc_xkn p) (s_regs ssX) (s_know ssX)) as [sg|] eqn:Hr; [|discriminate].
  apply andb_true_iff in H as [H1 H2]. exists sg. split; [exact H1|]. split; [exact H2|].
  eapply rematch_from_dom; [exact Hr | exact Hd0].
Qed.

(* [comment removed for export] *)
Theorem Pgen_of_check_any : ltac2:(zQ "hf0!me!i3!hr5!n5!he!hra!ihe!isd!lu7!hva!ig3!vc!lv0!hs1!ht1!h8!ih3!ih9!lve!mga!mh3!mhd!mi7!mj3!mne!im9!mk8!mqf!igc!mm4!mn1>0$hd>0$he>1p$h7>5extra>0$b$3>2sh@1$f@2$1$4$0>0@3$7$3@2$h8^3^2$6>0@2$hb@1$8^4@1$h3^4>0@3$7$3@3$d@2$1@2$1$0$2$2\1r@2$1@2$1$0$2$2M1\1r@2$1@2$1$0$2$2$3^1\1y@2$1$0$2\2y0$2M1\1y@2$1$0$2$3^2\2y1$0\2y2$2M0\2y1$0$3^2\1z$2$6\1n$4@1$h0@2$hc^1@1$8^b\2op$9\1a$0\1b$0$5\2op$9\1a$0\1b$0$5\2op$a\1a$0\1b$0$5\2op$a\1a$0\1b$0$5\2sx$3\2lo$4\1n$4\1e$0$5\2sx$3\1k$4\1i$2\1n$4$5@1$c^5$6>0>2sg$b>0@3$7$3@1^6^1$6@3$7$3@3$d@2$1$4$0\2ne@2$1$4$0@3$h9^3@3$e$4$0^1@3$h1$4$0^1^6$6@7$ha@1$h2^7@1$h5^7@1$h6^7@1$h4^7@1$c^7@1$8^7^5").
Proof.
  intros COPY FILL p extra sh H Hd0 Hrg Hsh.
  destruct (piece_check_sound_dom _ _ H Hd0) as (sg & Hok & Hex & Hdom).
  apply (Pgen_of_piece COPY FILL (set_sg p sg) sh Hok).
  unfold shape_holds. cbn [set_sg pc_pv pc_regions pc_sg].
  rewrite (Hsh sg Hex), (dom_in_forallb _ _ Hdom), Hrg. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition slot_var : ltac2:(zQ "10!he>1k$0$0") := ltac2:(zQ "40!he!mve!nhc!ni3\1k$0@2$1Ni0@4$2$0^1$3N0").
Definition step_shape : ltac2:(zQ "20!nme!hk9>2st$0$1") := ltac2:(zQ "h20!he!me!nn6!ju7!i3!n5!mq1!nnd!mve!no9!np0!np7!nq2!nme!nqd!nrc!ns3!nsa\2st$d@3$6@2$4$0$1@4$3$0$1Ni0@1$2Nme@3$6@2$4$0$1@4$3$0$1Ni2@3$f$b@1$2Ni2@1$h0@1$c^1@4$9$0@2$4$0$1\1k$0@4$3$0$1@1$7^1M5\0$5$1@2$h1^1@1$e^2@1$2@2$8Nmf^1@1$2@1$7^1@2$aN0Nc").
(* [comment removed for export] *)
Definition keep_shape : ltac2:(zQ "10!hk9$0") := ltac2:(zQ "b0!he!me!i3!ju7!nn6!mq1!nnd!nt0!ju2!no9!np0@3$7@2$2$0$1@4$9$0@2$2$0$1\1k$0@4$3$0$1@1$6^1@1$4@1$6^1@2$aN0Nc@3$5@2$2$0$1@4$3$0$1Ni2@1$4Ni2@3$5@2$2$0$1@4$3$0$1Ni0@1$4Ni0@1$8@2$2$0$1").
(* [comment removed for export] *)
Definition throw_shape : ltac2:(zQ "10!hk9$0") := ltac2:(zQ "h00!he!me!nn6!ju7!i3!n5!mq1!mve!nt5!no9!np0!np7!nnd!nrc!ns3!nsa@3$6@2$4$0$1@4$3$0$1Ni0@1$2No4@3$6@2$4$0$1@4$3$0$1Ni2@3$d$b@1$2N0@1$e+nk0@4$9$0@2$4$0$1\1k$0@4$3$0$1@1$c^1M5\0$5$1@2$f^1N8@1$2@2$7Nnc^1@1$2@2$7Nh4@2$8^1N8@2$aN0Nc").
(* [comment removed for export] *)
Definition resume_shape : ltac2:(zQ "20!nme!hk9>2st$0$1") := ltac2:(zQ "h40!he!me!nn6!n5!ju7!i3!mve!mq1!nsa!nt5!no9!np0!np7!nq2!nme!nqd!nnd!nrc!ns3!nv4\2st$e@3$7@2$5$0$1@4$4$0$1Ni0@1$2Nme@3$7@2$5$0$1@4$4$0$1Ni2@3$h1$c@1$2N0@1$h2@2$h3+ko0@1$d^1@4$a$0@2$5$0$1\1k$0@4$4$0$1@1$h0^1M3\0$3$1@2$8^1@1$f^2@1$2@2$6Nmf^1M3\0$3$1@2$8^1N8@1$2@2$6Nnc^1@1$2@2$6Nh4@2$9^1N8@2$bN0Nc").

(* [comment removed for export] *)
Lemma shape_ok_step_shape : ltac2:(zQ "e0!he!me!n5!i3!ihe!isd!ht1!ih9!nme!vc!im9!nvb!og7!hs1>2ph$2>2st$8>2sg$9>0@3$5$2@3$b^3^2^1$4@3$5$2@3$d@2$3$0$1\2ne@2$3$0$1@3$a^3@3$6$0$1^1@3$7$0$1^1@1$c^3$4").
Proof.
  intros ph st sg H. unfold shape_ok in H.
  apply andb_true_iff in H as [H Hfix]. apply andb_true_iff in H as [H Hslots]. apply andb_true_iff in H as [Hip Hsp].
  unfold step_shape. cbn [forallb fst snd]. rewrite Hip, Hsp. cbn [andb].
  rewrite forallb_forall. intros ne Hin. apply in_map_iff in Hin as (k & <- & Hk). cbn [fst snd].
  rewrite forallb_forall in Hslots. specialize (Hslots k Hk). cbn beta in Hslots. unfold slot_var. exact Hslots.
Qed.

Theorem Pcont_gen_of_check : ltac2:(zQ "h50!n5!he!ju2!i3!ihe!isd!oh5!oi0!oi6!oie!oj8!nme!mne!ok5!ol3!nvb!mk8!og7!mm4!mn1!me>0$h2>0$h3>2ph$0>2cf$0>2st$b>4fuel$1>0@3$5$0@2$c@5$d^4^3^2^1@1$2@2$3$1$h4@2$f^4^2$4@7$h0@3$8^5^4^3$6@1$a^5@1$9^5@1$e^5$7@1$h1^3").
Proof.
  intros COPY FILL ph cf st fuel H.
  apply (Pgen_of_check_any COPY FILL (cont_piece ph cf st fuel []) (shape_ok ph st) (step_shape st) H).
  - intros n e Hin. destruct Hin.
  - destruct ph; vm_compute; reflexivity.
  - intros sg Hsg. eapply shape_ok_step_shape. exact Hsg.
Qed.

End PIECEQ.
