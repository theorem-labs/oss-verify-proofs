(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes Frame AgentLib FileSim
  SymExec2 SymExec2Sound SymRun SymDrive SymDriveX MemSplit Spec LibTail RefPrintfLib RefMemcpyLib
  SReach RegsEquivM MainEqv HeapCeil MainMem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Arr Step Frame MState SysStep Exec CellsX TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsStack0
  AsPrintfFirst AsDrvDefs AsDrvMem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~k14cell37Corelib4Init9Datatypeso44conso43nilo46option37Corelib4Init5Logicr22ex79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~sb5asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As7AsIface~~~~~~hge6AERRNOk12C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~hla8rw_cells01Zo44prodo43fsto44listo43sndr22or37Corelib5Lists7ListDefhs36Forall79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hu47outside46Stdlib6ZArith6BinInt1Ziib2leiib2lthu4ddisjoint_fromiib3addo44Somer22eq69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~in33rdn69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~ir5floaded_segmentsiib6of_nathf7Z_to_bvo43natr23andhu43ivlhu45munchiib3pow79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~jj48cells_oko44boolo44truejj49cell_wf_b36Stdlib5Lists4Listjqc7forallbhge3memhgecaclient_addrhge5apreshge5blockhgebaimg_client79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As9AsDrvDefs~~~~~~kg2aadrv_cellskg28astdout0jj47cell_okjqc2Injqc4inclk1bcells_bytesk1acells_sizeo44pairk12C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~kpb2wzk12C1kpb2b8sbcASHADOW_BASEiib3div79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As8AsStack0~~~~~~kvd6stack0iib3subhge3asr" s.   (* [comment removed for export] *)
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Asan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Ltac in_solve := cbn [In]; repeat (first [ left; reflexivity | right ]).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma aerrno_rw_any : ltac2:(zQ "b0!h9!jc!nd!pc!q3!q9!s6!hg6!hkb!hl5!hp5>1m>0@1$1@1$0#k0@1$5@1$1@1$0#8@2$6@1$1@1$0#k0\1e@1$1@1$0#k0@4$a$7^2$8@3$3$2@1$9^1@1$4$2").
Proof.
  intros m. unfold AERRNO, ATP. change (0x6f43d8 - 0xa4) with 0x6f4334.
  assert (RD : forall i, 0 <= i < 4 -> exists b, mrd asegs m (wa (0x6f4334 + i)) = Some b).
  { intros i Hi. unfold mrd. destruct (m (wa (0x6f4334 + i))) as [b|]; [exists b; reflexivity|].
    rewrite seg_rom_same. change asegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; eexists; reflexivity. }
  destruct (RD 0 ltac:(lia)) as [b0 H0]. destruct (RD 1 ltac:(lia)) as [b1 H1].
  destruct (RD 2 ltac:(lia)) as [b2 H2]. destruct (RD 3 ltac:(lia)) as [b3 H3].
  exists (Z_to_bv 64 (bytes_le_to_Z [b0; b1; b2; b3])).
  split.
  - split; [cbn; repeat split; exact I|]. cbn [cells_bytes cbytes app].
    change (le4 ?v) with (word_to_le_bytes 4 v). rewrite word_to_le_bytes_of_lez by (reflexivity || (cbn; lia)).
    rewrite app_nil_r. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi.
    destruct i as [|[|[|[|i]]]]; cbn [nth_error Z.of_nat Pos.of_succ_nat Pos.succ]; [ | | | | lia].
    + rewrite Z.add_0_r in H0. exact H0. + exact H1. + exact H2. + exact H3.
  - split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn [cells_size csize Nat.add] in Hi.
    unfold wview. destruct (m (wa (0x6f4334 + i))) as [b|]; [discriminate|].
    change asegs with RSEGS.
    assert (H4 : i = 0 \/ i = 1 \/ i = 2 \/ i = 3) by lia.
    destruct H4 as [->|[->|[->| ->]]]; vm_compute; discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma outside_of_Forall : ltac2:(zQ "a0!hq1!hq4!hqb!hr1!hr8!hre!hta!ii0!ik3!ik9>1W@1$3@2$1$0$0>1x$0>0@3$6@2$1$0$0\2iv@2$1$0$0@2$5@2$9^2@3$2$0$0^1@2$8@3$4$0$0^1^2^2@2$7^3^2").
Proof.
  induction W as [|[l h] W IH]; intros x HF; [exact I|]. inversion HF as [|y l' Hy Hl]; subst.
  cbn [fst snd] in Hy. cbn. split; [lia | apply IH; exact Hl].
Qed.
Lemma disjoint_of_Forall : ltac2:(zQ "a0!hq1!hq4!ik3!hqb!hr1!hr8!hre!hta!ikf!im0>1W@1$4@2$1$0$0>1a$0>1n$0>0@3$7@2$1$0$0\2iv@2$1$0$0@2$6@2$2@2$9^3^2@3$3$0$0^1@2$2@3$5$0$0^1^3^3@3$8^4^3^2").
Proof.
  induction W as [|[l h] W IH]; intros a n HF; [exact I|]. inversion HF as [|y l' Hy Hl]; subst.
  cbn [fst snd] in Hy. cbn. split; [lia | apply IH; exact Hl].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rdn_munchW : ltac2:(zQ "h41!h9!jc!hr1!q9!ik3!im7!ime!hq1!iqe!iua!im0!ivd!jg7!jh1!jh7!jhd!ji4!ii0!ik9!jid&>0@1$1@1$0#k0@1$3@1$1@1$0#8>1W@1$2$f>1m~0>2m'~0>1a$7>1n$d>2bs@1$2@1$1@1$0#8>0@3$h0^6^5^4>0@3$6@1$3@1$2@1$1@1$0#8@4$8$9^6@2$c@1$0#k0^4^3@2$5@1$2@1$1@1$0#8^2>0@2$4Z^5>0@2$4@2$a^6@1$b^5@2$h3+2+k0>0>1x$7>0@2$e@2$4^8^1@2$h2^1@2$a^8@1$b^7@2$h1^c^2@3$6@1$3@1$2@1$1@1$0#8@4$8$9^9@2$c@1$0#k0^8^7@2$5@1$2@1$1@1$0#8^6").
Proof.
  intros W m m' a n bs MU HD Ha Hn HO.
  destruct n as [|n']; [cbn in *; exact HD|].
  rewrite (rdn_ext RSEGS (S n') m' m); [exact HD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia.
  apply MU. apply HO. exact Hx.
Qed.

Lemma cells_ok_munchW : ltac2:(zQ "h21!hq4!hq1!jh1!h9!jc!hr1!q9!jo5!jp1!jp8!ime!hta!jpf!ikf!jhd!ji4!jrf!ivd&>0@1$4@1$3#k0@1$6@1$4@1$3#8>1W@1$5$e>1m~0>2m'~0>2cs@1$5@2$0@2$0$1$2$1>0@3$a$8@3$h0@2$0@2$0$1$2$1$c^1$9>0@2$7^4^2>0@3$f^6^5^4>0@3$b@2$0@2$0$1$2$1\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1P^1\1p@2$0$1$2\1z$1M0\1p@2$0$1$2P^2\1a$1\1w$2@3$d^c^2@1$h1^1^4@2$7^6^5").
Proof.
  intros W m m' cs Hwf Hc MU Hd. unfold cells_ok in *.
  induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_ok in *. eapply rdn_munchW; [exact MU | exact Hok | lia | lia |]. intros y Hy. eapply disjoint_outside; [exact Hx | lia].
Qed.
End FPX1.

Section Apres.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Variable H : ltac2:(zQ "10!lkc$0").
  Lemma rdn_apresW : ltac2:(zQ "h50!h9!hr1!jc!hq1!ik3!im7!q9!ime!jsa!iqe!iua!im0!ivd!jg7!jh1!jh7!jt1!ju1!jua!ik9!jid>3LB1@1$1$h2>2SP$3>1m$8>2m'$8>1a$3>1n$e>2bs@1$1@1$2@1$0#8>0@6$h1?5HCEIL?1H^7^6^5^4>0@3$7@1$6@1$1@1$2@1$0#8@4$9$a^6@2$d@1$0#k0^4^3@2$5@1$1@1$2@1$0#8^2>0@2$4Z^5>0@2$4@2$b^6@1$c^5@2$h4+2+k0>0>1x$3>0@2$f@2$4^8^1@2$h3^1@2$b^8@1$c^7@5$h0?5HCEIL?1H^d^c^2@3$7@1$6@1$1@1$2@1$0#8@4$9$a^9@2$d@1$0#k0^8^7@2$5@1$1@1$2@1$0#8^6").
  Proof.
    intros LB1 SP m m' a n bs HP HD Ha Hn HC.
    destruct n as [|n']; [cbn in *; exact HD|].
    rewrite (rdn_ext RSEGS (S n') m' m); [exact HD | rewrite u_small by lia; lia |]. intros x Hx. rewrite u_small in Hx by lia.
    rewrite <- (Z_to_bv_bv_unsigned x), <- wa_eq. exact (proj1 (HP _ (u64_range x) (HC _ Hx))).
  Qed.

  Lemma cells_ok_apresW : ltac2:(zQ "h70!hq1!hq4!jh1!hr1!h9!jo5!jc!jp1!q9!jp8!jh7!ime!hta!jv3!ju1!jua!jsa!jpf!jrf!im0!ik3!ik9!ivd>3LB1@1$3$f>2SP$0>1m>0@1$6@1$4#k0@1$8@1$6@1$4#8>2m'$h0>2cs@1$3@2$1@2$1$0$2$0>0@3$b$7@3$h2@2$1@2$1$0$2$0$h1^1$9>0@2$5^4^2>0@6$e?5HCEIL?1H^7^6^5^4>0@3$c@2$1@2$1$0$2$0\1c@2$1@2$1$0$2$0M1\1c@2$1@2$1$0$2$0P^1\1p@2$1$0$2\1z$0M1\1p@2$1$0$2P^2\1a$0\1w$2>1x$0>0@2$a@2$h4^3^1@2$h5^1@2$h3^3@1$h6^2@1$d^2^4@2$5^6^5").
  Proof.
    intros LB1 SP m m' cs Hwf Hc HP Hd. unfold cells_ok in *.
    induction cs as [|[[a w] v] cs IH]; [constructor|].
    cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
    inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
    unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
    repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
    unfold cell_ok in *. eapply rdn_apresW; [exact HP | exact Hok | lia | lia |]. intros y Hy. right; left. apply Hx. exact Hy.
  Qed.
End Apres.

Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma adrv_cells_client : ltac2:(zQ "b0!hq1!hq4!jh1!jh7!hta!kk1!jv3!im0!ik3!ik9!ivd@3$4@2$1@2$1$0$2$0\1c@2$1@2$1$0$2$0M1\1c@2$1@2$1$0$2$0P^1\1p@2$1$0$2\1z$0M1\1p@2$1$0$2P^2\1a$0\1w$2>1x$0>0@2$3@2$8^3^1@2$9^1@2$7^3@1$a^2@1$6^2$5").
Proof. unfold adrv_cells, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.
Lemma astdout0_client : ltac2:(zQ "b0!hq1!hq4!jh1!jh7!hta!kkf!jv3!im0!ik3!ik9!ivd@3$4@2$1@2$1$0$2$0\1c@2$1@2$1$0$2$0M1\1c@2$1@2$1$0$2$0P^1\1p@2$1$0$2\1z$0M1\1p@2$1$0$2P^2\1a$0\1w$2>1x$0>0@2$3@2$8^3^1@2$9^1@2$7^3@1$a^2@1$6^2$5").
Proof. unfold astdout0, aimg_client. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; intros; lia|]). apply Forall_nil. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma adrv_cells_wf : ltac2:(zQ "90!hq4!hq1!jp1!jh1!jp8!ime!kk1!jpf!jrf@3$5$2@3$8@2$0@2$0$1$3$1$7$6$4"). Proof. vm_compute. reflexivity. Qed.
Lemma adrv_cells_range : ltac2:(zQ "b0!hq1!hq4!jh1!jh7!ime!ik3!hre!im0!ivd!hta!kk1@3$9@2$1@2$1$0$2$0\1c@2$1@2$1$0$2$0M1\1c@2$1@2$1$0$2$0P^1\1p@2$1$0$2\1z$0M1\1p@2$1$0$2P^2\1a$0\1w$2@2$6@2$3@2$5+hrnjq0^2@2$5@2$7^2@1$8^1+hrpvpc@2$6@2$3@3$4$0^2+hrsrt0@3$4$2^1N1@2$6@2$3@2$5+nhkkic^2@2$5@2$7^2@1$8^1+nhkmmc@2$3@3$4$0^2+nhkru0@3$4$2^1N8$a").
Proof. unfold adrv_cells. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.
Lemma astdout0_wf : ltac2:(zQ "90!hq4!hq1!jp1!jh1!jp8!ime!kkf!jpf!jrf@3$5$2@3$8@2$0@2$0$1$3$1$7$6$4"). Proof. vm_compute. reflexivity. Qed.
Lemma astdout0_range : ltac2:(zQ "90!hq4!hq1!jh1!ik3!jh7!hta!kkf!im0!ivd@3$5@2$0@2$0$1$2$1\1c@2$0@2$0$1$2$1M0\1c@2$0@2$0$1$2$1P^1\1p@2$0$1$2\1z$1M0\1p@2$0$1$2P^2\1a$1\1w$2@2$4@2$3+hrpvv8^2@2$3@2$7^2@1$8^1+hrqgoc$6").
Proof. unfold astdout0. repeat (apply Forall_cons; [cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]). apply Forall_nil. Qed.

Lemma cells_ok_In : ltac2:(zQ "a0!hq4!hq1!jh1!h9!jc!hr1!q9!klb!jo5!km6>1m>0@1$4@1$3#k0@1$6@1$4@1$3#8>2cs@1$5@2$0@2$0$1$2$1>1c@2$0@2$0$1$2$1>0@2$8^3^2>0@3$9@2$0@2$0$1$2$1^2^3@2$7^5^3").
Proof. intros m cs c CO IN. exact (proj1 (Forall_forall _ _) CO _ IN). Qed.
Lemma cells_ok_incl : ltac2:(zQ "90!hq4!hq1!jh1!hr1!h9!jo5!jc!q9!kmc>1m>0@1$6@1$4#k0@1$7@1$6@1$4#8>2c1@1$3@2$0@2$0$1$2$1>2c2@1$3@2$0@2$0$1$2$1>0@2$5^3^1>0@3$8@2$0@2$0$1$2$1^3^2@2$5^5^4").
Proof. intros m c1 c2 H2 HI. apply Forall_forall. intros c Hc. exact (cells_ok_In _ _ _ H2 (HI _ Hc)). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rw_rdn : ltac2:(zQ "f0!h9!jc!hr1!q9!im7!ime!hq1!hg6!nd!kn4!ko2!hp5!iqe!iua!jg7>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a$6>2cs@1$2$8>0@4$b$7^3^2^1@3$5@1$3@1$2@1$1@1$0#8@4$c$d^4@2$e@1$0#k0^3@1$a^2@2$4@1$2@1$1@1$0#8@1$9^2").
Proof.
  intros m a cs [[WF BA] _].
  pose proof (bytes_at_rdn asegs m a (cells_bytes cs) 0 (cells_size cs) BA) as R.
  rewrite Z.add_0_r, firstn_all2 in R; [| cbn [skipn]; rewrite cells_bytes_length by exact WF; lia].
  apply R. cbn [skipn]. rewrite cells_bytes_length by exact WF. lia.
Qed.
Lemma cell_of_C8 : ltac2:(zQ "f0!hq1!jh1!kof!h9!nd!jc!pc!q3!q9!hq4!hg6!klb!kp6!hp5!kt6>1m>0@1$5@1$3#k0@1$8@1$5@1$3#8>1a$0>1v$0>0@4$d$a^3^2@3$6$4@1$c@1$e^1@1$7$4@2$b^4@4$2@2$9$0$1$0@4$2$0$1^3N8^2").
Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.
Lemma cell_of_C4 : ltac2:(zQ "f0!hq1!jh1!kof!h9!nd!jc!pc!q3!q9!hq4!hg6!klb!hl5!hp5!kt6>1m>0@1$5@1$3#k0@1$8@1$5@1$3#8>1a$0>1v$0>0@4$d$a^3^2@3$6$4@1$c@1$e^1@1$7$4@2$b^4@4$2@2$9$0$1$0@4$2$0$1^3N4^2").
Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. unfold cell_ok. cbn [cells_size csize Nat.add] in R. rewrite R. cbn [cells_bytes cbytes app]. rewrite app_nil_r. reflexivity. Qed.
Lemma cells_of_C8C8 : ltac2:(zQ "h40!hq1!jh1!kof!nd!pc!hq4!h9!klb!kp6!kt6!im0!jc!q3!q9!jh7!hg6!hp5!ik3!ik9!jid>1m>0@1$b@1$6#k0@1$d@1$b@1$6#8>1a$0>2v1$0>2v2$0>0@4$h0$f^4^3@3$4$3@1$8@1$9^2@3$4$3@1$8@1$9^1@1$c$3>0@2$h1Z^4>0@2$h2@2$a^5+h0@2$h3+2+k0@2$e@2$7^7@4$2@2$5$0$1$0@4$2$0$1^6N8^5@2$7^7@4$2@2$5$0$1$0@4$2$0$1@2$a^6+8N8^4").
Proof.
  intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. unfold cell_ok. split.
  - pose proof (rdn_firstn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R1. rewrite R1. cbn [cells_bytes cbytes app].
    rewrite firstn_app, length_le8, Nat.sub_diag, firstn_O, app_nil_r, firstn_all2 by (rewrite length_le8; lia). reflexivity.
  - pose proof (rdn_skipn RSEGS m 16 (Z_to_bv 64 a) _ 8 R ltac:(lia)) as R2. unfold nat_to_word in R2.
    change (16 - 8)%nat with 8%nat in R2. replace (Z.of_nat 8) with 8 in R2 by reflexivity. rewrite lit_add_lit in R2.
    rewrite R2. cbn [cells_bytes cbytes app]. rewrite app_nil_r. rewrite (drop_app_length' _ _ 8) by (rewrite length_le8; reflexivity). reflexivity.
Qed.
Lemma cells_of_C1C1 : ltac2:(zQ "h60!h9!jc!pc!hr1!jg7!q3!q9!hq1!nd!im7!ime!ktc!ku1!iqe!iua!im0!jh7!hg6!hp5!ik3!ik9!jid>1m>0@1$1@1$0#k0@1$6@1$1@1$0#8>1a$7>2v1$7>2v2$7>0@4$h2$h1^4^3@3$2$8@1$b@1$c^2@3$2$8@1$b@1$c^1@1$5$8>0@2$h3Z^4>0@2$h4@2$f^5+2@2$h5+2+k0@2$h0@3$a@1$6@1$3@1$1@1$0#8@4$d$e^7@2$4@1$0#k0^6N1@2$9@1$3@1$1@1$0#8@3$2@1$1@1$0#8@2$4@1$0#8^5@1$5@1$1@1$0#8@3$a@1$6@1$3@1$1@1$0#8@4$d$e^7@2$4@1$0#k0@2$f^6+1N1@2$9@1$3@1$1@1$0#8@3$2@1$1@1$0#8@2$4@1$0#8^4@1$5@1$1@1$0#8").
Proof.
  intros m a v1 v2 RC Ha Ha2. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. split.
  - pose proof (rdn_firstn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R1. rewrite R1. reflexivity.
  - pose proof (rdn_skipn RSEGS m 2 (Z_to_bv 64 a) _ 1 R ltac:(lia)) as R2. unfold nat_to_word in R2.
    change (2 - 1)%nat with 1%nat in R2. replace (Z.of_nat 1) with 1 in R2 by reflexivity. rewrite lit_add_lit in R2.
    rewrite R2. reflexivity.
Qed.
Lemma cell_of_C1 : ltac2:(zQ "h10!h9!jc!pc!hr1!q3!q9!hq1!nd!jg7!im7!ime!hg6!ktc!hp5!ku1!iqe!iua>1m>0@1$1@1$0#k0@1$5@1$1@1$0#8>1a$6>1v$6>0@4$d$b^3^2@3$2$7@1$c@1$e^1@1$4$7@3$a@1$5@1$3@1$1@1$0#8@4$f$h0^4@2$8@1$0#k0^3N1@2$9@1$3@1$1@1$0#8@3$2@1$1@1$0#8@2$8@1$0#8^2@1$4@1$1@1$0#8").
Proof. intros m a v RC. pose proof (rw_rdn m a _ RC) as R. cbn [cells_size csize Nat.add] in R. rewrite R. reflexivity. Qed.
End FPX2.

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Q.
  Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
  Context {HCEIL : HeapCeil}.
  Lemma stack0_qsh0 : ltac2:(zQ "h00!h9!hq1!im0!ik3!ku7!kv6!jg7!jc!im7!q9!jh7!ime!jsa!ljb!ik9!lk5>1m$c>2lo$1>2hi$1>3sp'$1>0@4$d?5HCEIL^4^3^2>0@2$3@2$2^4+hgg8^2>0@2$3^3^4>1a$1>0@2$a@2$3@2$2$4@2$5@2$f^5+hgg0+8^1@2$e^1@2$2$4@2$5^5+8@3$b@1$9@1$7@1$0#8@1^9@2$6@1$0#k0^2@2$8@1$7@1$0#8@2$6@1$0#8Z").
  Proof.
    intros m lo hi sp' ST Hlo Hhi a Ha. pose proof (stack0_bounds _ _ _ ST) as [B1 B2]. acb. rewrite ASHADOW_BASE_val in Ha.
    set (x := 8 * (a - 0x7fff8000)).
    assert (Hx : lo <= x /\ x + 1 <= hi) by (subst x; Z.div_mod_to_equations; lia).
    assert (Ex : wa (sh x) = Z_to_bv 64 a).
    { unfold wa, sh. rewrite ASHADOW_BASE_val. f_equal. subst x. Z.div_mod_to_equations. lia. }
    pose proof (stack0_read0 m lo hi x 1 (Z_to_bv 64 a) ST ltac:(lia) ltac:(lia) ltac:(lia) ltac:(symmetry; exact Ex)) as RD.
    rewrite ov_rdn in RD. cbn [rdn Lib.PropExec.rdn] in RD. unfold mrd in RD.
    destruct (m (Z_to_bv 64 a)) as [b|] eqn:E.
    - cbn in RD. unfold TacX.b8 in RD. congruence.
    - exfalso. change asegs with RSEGS in RD. rewrite (aseg_rom_high (Z_to_bv 64 a)) in RD; [discriminate|].
      rewrite u_small; [lia | unfold AAPP_HI in *; lia].
  Qed.
End Q.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
