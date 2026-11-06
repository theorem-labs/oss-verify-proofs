(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require As0Gc3. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.boost_json.fuzz_parse.images Require Import Asan.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg Nodes AgentLib Frame HeapCeil SymExec2 SymExec2Sound SymRun RefPrintfLib MemSplit LibTail MainMem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Mem Cells Step Frame MState SysStep Exec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.As Require Import ASegs AsShadow AsConst AsIface AsPrintfFirst.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv37Corelib4Init9Datatypesk16option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As5ASegs~~~~~~m25asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~q55wmono69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7StoreOk~~~~~~u99mem_growsk14listk14prod01Z69OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Frame~~~~~~hk09frame_mod3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeho57Segmentk14bool46Stdlib6ZArith6BinInt1Zhsc3lebk14Somek14andbhsc3addk14None37Corelib4Init5Logicig72eq3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsii1cfind_segment59OSSVerifyaboost_jsonafuzz_parse6images4Asan~~~~~~im8h0Asan_segment_000im8h0Asan_segment_001im8h0Asan_segment_002im8h0Asan_segment_003hfbbv_unsignedk14trueig73and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~jgb7ro_addrhsc2lehsc2ltk15falseig72orjgb7mem_invhf7Z_to_bvk13fstk13snd37Corelib5Lists7ListDefjob6Forallhsc3powhsc6of_natk13natig73notii18store_okii15wview69OSSVerifyaboost_jsonafuzz_parse6images4Asan1M~~~~~~jtffloaded_segmentsq53stk69OSSVerify6Proofsaboost_jsonafuzz_parse3lib6SymRun~~~~~~kid6stk_okhsc3sub69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~kn77seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2As0d1A1s1P1r1i1n1t1f1F1i1r1s1t~~~~~~krd8cells_okkrd9cell_wf_b36Stdlib5Lists4Listli72Inli77forallbkn73rdn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ll28rw_cells79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~lp94celllp9acells_size" s.   (* [comment removed for export] *)
Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.
Import ListNotations.
Import SymExec2.SX2. Import SymExec2Sound.SX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Open Scope Z_scope.

Abbreviation RSEGS := Asan.M.loaded_segments.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma amem_grows_wmono : ltac2:(zQ "61!h9!jc!l9!pd!u1!hi3&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>0@2$5^2^1@3$4$3^3^2").
Proof.
  intros m m' Hg x Hw. unfold wview in *. destruct (m x) as [b|] eqn:E.
  - assert (m' x <> None) as H' by (apply Hg; congruence). destruct (m' x); [discriminate|contradiction].
  - destruct (m' x); [discriminate|]. exact Hw.
Qed.
Lemma aframe_mod_wmono : ltac2:(zQ "91!h9!jc!l9!hif!hj6!hjd!pd!hn8!u1&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>2rs@1$3@2$4@1$1@1$0#k0$5>0@3$7^3^2^1@3$8$6^4^3").
Proof. intros m m' rs [_ Hg]. apply amem_grows_wmono. exact Hg. Qed.

Lemma find_segment_asegs : ltac2:(zQ "h00!hra!hs5!hu4!l9!hub!hv2!hv9!ig0!ihb!hjd!il8!pd!ipb!ir0!is5!ita>1x$9@3$8@1$3$0@3$a$b^1+1M1\0$1@1$3$0@2$5@2$2+hggg0^1@2$2@2$6^1+1+mngg0@2$4$0$cM1\0$1@1$3$0@2$5@2$2+mngg0^1@2$2@2$6^1+1+hqtgg0@2$4$0$dM1\0$1@1$3$0@2$5@2$2+hqtgg0^1@2$2@2$6^1+1+hrngg0@2$4$0$eM1\0$1@1$3$0@2$5@2$2+hrngg0^1@2$2@2$6^1+1+nhmgg0@2$4$0$f@1$7$0").
Proof. intros x. reflexivity. Qed.

Lemma aro_addr_true : ltac2:(zQ "b0!h9!iuf!hs5!ivd!jg4!ihb!pd!jk5!jl0!jl6!jc>1a@1$a@1$0#k0>0@2$4@2$8+hggg0@2$1@1$0#k0^1@2$9@2$1@1$0#k0^1+hqtgg0@3$5$2@2$7$6^2$3").
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x67000); cbn [andb]; [reflexivity| | lia | lia].
  destruct (Z.leb_spec 0x67000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x1ad000); cbn [andb]; [reflexivity| lia | lia | lia].
Qed.

Lemma aro_addr_false : ltac2:(zQ "b0!h9!iuf!hs5!jlc!ihb!jm4!pd!jk5!jl0!jl6!jc>1a@1$a@1$0#k0>0@2$5@2$9@2$1@1$0#k0^1+hggg0@2$8+hqtgg0@2$1@1$0#k0^1@3$4$2@2$7$6^2$3").
Proof.
  intros a Ha. unfold ro_addr. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x67000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x67000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x1ad000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x1ad000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x1b7000); cbn [andb]; try lia; try reflexivity;
  destruct (Z.leb_spec 0x1b7000 (bv_unsigned a)); destruct (Z.leb_spec (bv_unsigned a + 1) 0x716000); cbn [andb]; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_ro_none : ltac2:(zQ "c0!h9!jc!l9!ig0!jg4!ihb!hjd!pd!jma!jl0!jl6!jn5>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>0@2$8$7^1>1i$6>0@2$4@2$9+hggg0^1@2$a^1+mngg0@3$5@1$2@1$1@1$0#8@1^4@2$b@1$0#k0^2@1$3@1$1@1$0#8").
Proof.
  intros m Hinv i Hi. destruct (m (Z_to_bv 64 i)) as [b|] eqn:E; [|reflexivity].
  pose proof (Hinv _ _ E) as Hro. rewrite aro_addr_true in Hro; [discriminate|]. rewrite u_small by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma amem_inv_frame : ltac2:(zQ "h23!h9!jc!hjd!jnf!hj6!jl0!iuf!l9!jo5!pd!jma!hv9!hif!jg4!jm4!jq2!hn8!jqc&>0@1$1@1$0#k0@1$7@1$1@1$0#8&@2$6@1$0#k0@3$3@1$1@1$0#k0$2^1&@2$b~1@3$8@1$1@1$0#k0$2^1>1m~0>2m'~0>2rs@1$c@2$4@1$1@1$0#k0$2>0@2$a$9^3>0@3$h0^4^3^2>0@3$f@2$4@1$1@1$0#k0$2\1r@2$4@1$1@1$0#k0$2@2$d@2$5~2@2$h1+2+k0@2$e@2$5~2+hggg0@2$5+hqtgg0~1^3@2$a$9^5").
Proof.
  intros m m' rs Hinv [Hout Hg] Hrs a b Hab.
  destruct (ro_addr asegs a) eqn:Ero; [|reflexivity]. exfalso.
  assert (Hcase : OSSVerify.Proofs.boost_json.fuzz_parse.lib.Frame.outside a rs \/ (bv_unsigned a < 0x10000 \/ 0x1ad000 <= bv_unsigned a)).
  { clear Hab Ero Hout Hg Hinv. induction rs as [|[r n] rs IH]; [left; exact I|].
    inversion Hrs as [|x l [Hnw Hr] Hl]; subst. cbn [fst snd] in Hnw, Hr.
    destruct (IH Hl) as [Ho|Hx]; [|right; exact Hx].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r)) as [Hlt|Hge]; [left; cbn; split; [unfold in_rng; lia|exact Ho]|].
    destruct (Z_lt_le_dec (bv_unsigned a) (bv_unsigned r + n)) as [Hin|Hout']; [|left; cbn; split; [unfold in_rng; lia|exact Ho]].
    right. lia. }
  destruct Hcase as [Ho|Hx].
  - rewrite (Hout a Ho) in Hab. pose proof (Hinv a b Hab). congruence.
  - rewrite aro_addr_false in Ero by exact Hx. discriminate.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma astore_ok_of_wview : ltac2:(zQ "h60!h9!jc!l9!ihb!hv9!jl6!jr3!iuf!ig0!hs5!jrd!ivd!jg4!js3!hjd!jsa!jt6!pd!kh4!jl0!jqc!jn5>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>1n$a>1a@1$1@1$0#k0>0@2$5@2$4@2$7@1$0#k0^1@1$6^2@2$h4+2+k0>0>1i$e>0@2$c@2$h3Z^1@2$5^1@1$6^4@1$d@3$3@1$2@1$1@1$0#8@3$h0$h1^6@2$h5@1$0#k0@2$4@2$7@1$0#k0^4^2@1$8@1$1@1$0#8@3$3$9@4$f$h2^5^3^4$b").
Proof.
  intros m n. induction n as [|n IH]; intros a Hn Hw; [reflexivity|].
  cbn [store_ok]. pose proof (u64_range a) as Ha.
  assert (W0 : wview asegs m a <> None).
  { pose proof (Hw 0 ltac:(lia)) as H0. rewrite Z.add_0_r, Z_to_bv_bv_unsigned in H0. exact H0. }
  unfold asegs, RefMemImage.Ref.loaded_segments in W0.
  destruct (wview RSEGS m a); [|contradiction].
  apply IH; [rewrite u_add1 by lia; lia|]. intros i Hi. rewrite u_add1 by lia.
  replace (bv_unsigned a + 1 + i) with (bv_unsigned a + (1 + i)) by lia. apply Hw. lia.
Qed.

Lemma astk_stk_ok : ltac2:(zQ "d0!h9!hjd!jl0!jc!iuf!l9!pd!ki7!km6!kh4!jl6!jqc!kn0>1m>0@1$3@1$0#k0@1$5@1$3@1$0#8>2lo$1>2hi$1>2sp@1$3@1$0#k0>1K$1>0@4$7$6^5^4^3>0@2$2^5@2$c@2$4@1$0#k0^3^2>0@2$2@2$4@1$0#k0^4^5>0@2$2Z^4>0@2$a^7@2$b+2+k0@4$8$9^a^7^6").
Proof.
  (intros m lo hi sp K nd_i1 Hlo Hhi HK Hhi2 a n Ha Hn; ndestruct nd_i1 as (H1 & H2 & H)). pose proof (u64_range a).
  apply astore_ok_of_wview; [lia|]. intros i Hi. rewrite <- wa_eq. apply (H (bv_unsigned a + i)). lia.
Qed.

Lemma aseg_rom_high : ltac2:(zQ "90!h9!jc!ig0!l9!ihb!kr2!kh4!jl0!iuf>1x@1$1@1$0#k0>0@2$7+nhmgg0@2$8@1$0#k0^1@3$4@1$3@1$1@1$0#8@2$5$6^2@1$2@1$1@1$0#8").
Proof.
  intros x Hx. unfold seg_rom, memory_read. change (Z.of_N 1) with 1%Z.
  change Asan.M.loaded_segments with asegs. rewrite find_segment_asegs.
  destruct (Z.leb_spec 0x10000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x67000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x67000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x1ad000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x1ad000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x1b7000); cbn [andb]; try lia;
  destruct (Z.leb_spec 0x1b7000 (bv_unsigned x)); destruct (Z.leb_spec (bv_unsigned x + 1) 0x716000); cbn [andb]; try lia; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma astk_grows : ltac2:(zQ "91!h9!jc!l9!hjd!pd!ki7!jl0!hi3!jqc&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1m~0>2m'~0>1l$3>1h$3>0@4$5$4^4^2^1>0@2$6+nhmgg0^3>0@2$6^3@2$8+2+k0>0@2$7^7^6@4$5$4^7^6^5").
Proof.
  (intros m m' l h nd_i2 Hl Hh Hg; ndestruct nd_i2 as (S1 & S2 & S3)). split; [exact S1|]. split; [exact S2|].
  intros x Hx. destruct (S3 x Hx) as [Hw [b Hb]].
  assert (E0 : exists b0, m (wa x) = Some b0).
  { unfold mrd in Hb. destruct (m (wa x)) as [b0|] eqn:E; [exists b0; reflexivity|].
    rewrite seg_rom_same in Hb. change asegs with RSEGS in Hb.
    rewrite aseg_rom_high in Hb; [discriminate|]. rewrite wa_eq, u_small by lia. lia. }
  destruct E0 as [b0 E0].
  assert (E1 : exists b1, m' (wa x) = Some b1).
  { destruct (m' (wa x)) as [b1|] eqn:E; [exists b1; reflexivity|]. exfalso. apply (Hg (wa x)); congruence. }
  destruct E1 as [b1 E1]. split.
  - unfold wview. rewrite E1. discriminate.
  - exists b1. unfold mrd. rewrite E1. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma acells_ok_frame : ltac2:(zQ "h72!hjd!hj6!h9!jc!jrd!jnf!hif!l9!lge!hv9!jl0!iuf!hs5!jo5!ivd!ihb!jm4!jq2!lha!hn8!lja!lk0!jr3&>0@1$3@1$2#k0@1$7@1$3@1$2#8&@2$b@1$2#k0@3$5@1$3@1$2#k0$0^2>1m~0>2m'~0>2rs@1$6@2$1@1$3@1$2#k0$0>2cs@1$6@2$1@2$1$0$4$0>0@3$f$c@3$h5@2$1@2$1$0$4$0$h2^1$e>0@2$8^5^2>0@3$h3^6^5^4>0@3$h1@2$1@2$1$0$4$0\1c@2$1@2$1$0$4$0M1\1c@2$1@2$1$0$4$0P^1\1p@2$1$0$4\1z$0M1\1p@2$1$0$4P^2\1a$0\1w$4>1r@2$1@1$3@1$2#k0$0>0@3$h4@2$1@1$3@1$2#k0$0^1^b@2$h0@2$a@2$9^4@1$h6^3~1@2$a@2$9~1@3$d@1$3@1$2#k0$0^2^4^4@2$8^7^5").
Proof.
  intros m m' rs cs Hwf Hc FM Hd. unfold cells_ok in *.
  induction cs as [|[[a w] v] cs IH]; [constructor|].
  cbn [forallb] in Hwf. apply andb_true_iff in Hwf as [H1 Hwf].
  inversion Hc as [|c cs' Hok Hc']; subst. inversion Hd as [|x l Hx Hl]; subst. constructor; [|apply IH; assumption].
  unfold cell_wf_b in H1. repeat (apply andb_true_iff in H1; destruct H1 as [H1 ?]).
  repeat match goal with H : (_ <=? _)%Z = true |- _ => apply Z.leb_le in H end.
  unfold cell_ok in *. rewrite <- Hok. apply (frame_mod_rdn RSEGS m m' rs w (Z_to_bv 64 a) FM); rewrite u_small by lia; [|lia].
  intros i Hi. apply outside_of_disjoint. intros r0 Hr0. pose proof (Hx r0 Hr0) as D. rewrite u_small by lia. lia.
Qed.

Lemma arange_none_frame : ltac2:(zQ "h41!h9!jc!hjd!jl0!l9!hj6!ig0!jnf!jg4!ihb!jl6!jn5!iuf!hif!jo5!jm4!hn8!lja!hv9!jqc&@2$c@1$0#k0@3$7@1$1@1$0#k0$2^2>1m>1x@1$1@1$0#k0@1$4@1$1@1$0#8>2m'>0@1$1@1$0#k0@1$4@1$1@1$0#8>2rs@1$d@2$5@1$1@1$0#k0$2>2lo$2>2hi$2>0>1i$2>0@2$8@2$3^3^1@2$a^1^2@3$9@1$4@1$1@1$0#8@1^7@2$b@1$0#k0^2@1$6@1$1@1$0#8>0@3$h0^6^5^4>0>1r@2$5@1$1@1$0#k0$2>0@3$h1@2$5@1$1@1$0#k0$2^1^6@2$f@2$3^5~0@2$3@2$h2~0@3$e@1$1@1$0#k0$2^2^6>0@2$3Z^5>0@2$3^5@2$h3+2+k0>1i$2>0@2$8@2$3^8^1@2$a^1^7@3$9@1$4@1$1@1$0#8@1^b@2$b@1$0#k0^2@1$6@1$1@1$0#8").
Proof.
  intros m m' rs lo hi Hn [Hout _] Hrs Hlo Hhi i Hi. rewrite Hout; [apply Hn; exact Hi|].
  apply outside_of_disjoint. intros r Hr. rewrite u_small by lia. destruct (Hrs r Hr); lia.
Qed.

Lemma ardn_frame : ltac2:(zQ "h72!h9!jc!hjd!hif!l9!hj6!hv9!jl0!hub!jnf!ihb!lkb!kh4!jr3!jn5!iuf!jrd!jo5!jm4!hn8!lja!jl6!jqc&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$f@1$0#k0@3$9@1$1@1$0#k0$2^2>1m~0>2m'~0>2rs@1$3@2$5@1$1@1$0#k0$2>1a$2>1n$h0>2bs@1$3@1$1@1$0#8>0@3$h3^6^5^4>0@3$a@1$4@1$3@1$1@1$0#8@4$b$c^7@2$e@1$0#k0^4^3@2$8@1$3@1$1@1$0#8^2>0@2$7Z^5>0@2$h5@2$6^6@1$d^5@2$h6+2+k0>0>1r@2$5@1$1@1$0#k0$2>0@3$h4@2$5@1$1@1$0#k0$2^1^9@2$h2@2$7@2$6^9@1$d^8~1@2$7@2$6~1@3$h1@1$1@1$0#k0$2^2^9@3$a@1$4@1$3@1$1@1$0#8@4$b$c^a@2$e@1$0#k0^8^7@2$8@1$3@1$1@1$0#8^6").
Proof.
  intros m m' rs a n bs FM HD Ha Hn Hrs. rewrite <- HD.
  apply (frame_mod_rdn RSEGS m m' rs n (Z_to_bv 64 a) FM); rewrite u_small by lia; [|lia].
  intros i Hi. apply outside_of_disjoint. intros r Hr. rewrite u_small by lia. destruct (Hrs r Hr); lia.
Qed.

(* [comment removed for export] *)
Lemma arw_cells_frame : ltac2:(zQ "h32!h9!jc!hjd!hj6!jnf!hif!l9!pd!lod!hv9!jl0!iuf!jo5!jm4!hn8!lt5!ltd!lja!jr3&>0@1$1@1$0#k0@1$6@1$1@1$0#8&@2$b@1$0#k0@3$4@1$1@1$0#k0$2^2>1m~0>2m'~0>2rs@1$5@2$3@1$1@1$0#k0$2>1A$2>2cs@1$5$f>0@4$8$7^5^2^1>0@3$e^6^5^4>0>1r@2$3@1$1@1$0#k0$2>0@3$h1@2$3@1$1@1$0#k0$2^1^6@2$d@2$a@2$9^6@1$h2@1$h0^5~1@2$a@2$9~1@3$c@1$1@1$0#k0$2^2^6@4$8$7^7^5^4").
Proof.
  intros m m' rs A cs RC FM Hrs.
  eapply rw_cells_transport; [exact RC | apply frame_mod_munch; exact FM | apply (aframe_mod_wmono _ _ _ FM) |].
  clear RC FM. induction rs as [|[r k] rs IH]; [exact I|]. cbn. split.
  - destruct (Hrs (r, k) (or_introl eq_refl)); cbn [fst snd] in *; lia.
  - apply IH. intros r' Hr'. apply Hrs. right. exact Hr'.
Qed.
End FPX1.
(* [comment removed for export] *)
