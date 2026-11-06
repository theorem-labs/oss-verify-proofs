(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_enframe F_mm_syscalls MallocTree MallocBlocks MallocHINV MallocFacts_B MallocFacts_B_reach.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocKit_B2 MallocModel_B MallocKit_B3 MallocFacts_Bpres F_ntf F_free_A F_free_B F_free_C.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_free_K.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~06mstate37Corelib7Numbers7BinNumsk61Z06regionk61N37Corelib4Init5Logicmf3and25stdpp9countableo9bN_countable35stdpp7numbers1Nq86eq_decmf2eq37Corelib4Init9Datatypess76optionmf2ex06r_base09s_regions25stdpp4basehg06lookup25stdpp4gmaphh64gmaphh6bgmap_lookups74Nones74Some07RKGroup06r_kind05r_len05rkind0bround_up_pg46Stdlib6ZArith6BinInt1Zhn33addhn32lehn32lt79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentcMallocBlocks~~~~~~hpe5blocks74listhpe8blk_slots74negb08aptr_eqb36Stdlib4Bool4Boolih07Is_truehg06filter25stdpp9decidableij7bIs_true_dec35stdppblist_basics4listil7blist_filterk64Npos35stdpp9bitvectorbdefinitionsio52bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent5F_ntf~~~~~~iq89oracle_ok79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8F_free_K~~~~~~iv36hdr_st79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~jje8ticks_ok04aptr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~jp29range_anss74bools74truemf4True79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaMallocTree~~~~~~jv19range_val0h0munmap_answer_okhn36modulojp28mmap_len" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition DROPPED : ltac2:(zQ "20!je!lf>2st$0>3st'$0>1a$1P") := ltac2:(zQ "h90!m3!mb!o3!pa!r9!s2!tf!u8!je!ud!v5!hgc!hi2!hia!hj9!hk0!lf!hk7!hl0!hl8!hlf!hm6!hob!hp2!hp8\2st$8\3st'$8\1a$h0@2$7$1\3rid$1@2$7$0\1r$0@2$2@3$5@1$6$0@6$b$1$0@4$c$1$4$3$0@4$d$1$4$3$0^2@1$a^5@2$f$0^1@2$2@3$5@1$6$0@6$b$1$0@4$c$1$4$3$0@4$d$1$4$3$0^2@1$a^4@1$e$0@2$2@3$5$h4@1$h2^1$h1@2$2@2$h7@1$9^1^3@2$h8^3@2$h6@1$9^1@1$h5@1$h3^1").

(* [comment removed for export] *)
Definition lbrm : ltac2:(zQ "20!hu3!huc>2LB@1$1$0>3blk$0@1$1$0") := ltac2:(zQ "90!hu3!hv3!huc!hvf!ig6!ii2!iid!ik8!imf\2LB@1$2$0\3blk$0@6$6$0@1$2$0@1$8$0\2b'$0@1$5@1$3@2$4@1$1^1@1$1^2\1x$0@1$7@1$3@2$4@1$1^1@1$1^2^2").

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma oracle_ok_refl : ltac2:(zQ "50!ine!iq2!tf!iu6!je>1m>0@1$1@1$0#k0@1$2@1$1@1$0#8>2st$4@3$3^2^2^1").
Proof. intros m st. intros rid r q h _ _ _ _ _. reflexivity. Qed.

Lemma oracle_ok_hdr_st : ltac2:(zQ "81!ine!iq2!tf!iu6!jj4!jo0!joc!je&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1o~0>1m~0>2st$7>2pf$6>0@1$5^2>0@3$3^5^4^3@3$3^6^5@2$4^4^3").
Proof. intros o m st pf.
  intros TK OK rid r q h Hr Hk Hq M8 Hc. change (s_regions (hdr_st st pf)) with (s_regions st) in Hr.
  rewrite hdr_st_cell_read in Hc by exact TK.
  destruct (N.eqb rid (fst pf) && ((q =? snd pf - 1) || (q =? snd pf - 2) || (q =? snd pf - 3)))%bool; [discriminate|].
  exact (OK rid r q h Hr Hk Hq M8 Hc).
Qed.

Lemma munmap_ok_range_val : ltac2:(zQ "a0!jsf!jtc!hp2!ju3!jua!o3!s2!lf!kj4!kk1>1a$0>0M0\1a$0P^1\1e$7@2$5@2$2+1^1@2$2^1+vvf\7changed$1$4@3$6$1@1$9@1$8^2$3").
Proof. intros a.
  destruct a as [e|c]; cbn [range_val]; intros He; unfold munmap_answer_ok, is_errno_form, neg_errno, TWO64.
  - apply orb_true_intro. right. apply andb_true_intro. split; [apply Z.leb_le| apply Z.ltb_lt]; lia.
  - reflexivity.
Qed.

Lemma round_up_pg_mod : ltac2:(zQ "40!lf!s2!hm6!kl4>1x$0@3$1$0@2$3@1$2^1+hgg0Z").
Proof. intros x. unfold round_up_pg, PGSZ. change (4096 - 1) with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12) with 4096. Z.div_mod_to_equations. lia. Qed.

Lemma mmap_len_round : ltac2:(zQ "40!lf!hm6!s2!kle>1x$0@3$2$0@1$3@1$1^1@1$1^1").
Proof. intros x.
  pose proof (round_up_pg_mod x) as M. unfold mmap_len, page_round_up_Z, page_size.
  set (y := round_up_pg x) in *. Z.div_mod_to_equations. nia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac cover_intervals tac :=
  let lo0 := fresh "ilo" in let hi0 := fresh "ihi" in let HW := fresh "HinW" in let y := fresh "y" in let Hy := fresh "Hy" in
  intros lo0 hi0 HW y Hy; cbn [In] in HW;
  repeat (destruct HW as [HW|HW]); try contradiction;
  injection HW; intros; subst lo0 hi0; tac y Hy.

Section FREE.
Variables (gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (LB : list block) (lo : Z).
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis GP : gp = Z_to_bv 64 0x1a800.
Hypothesis TP : tp = Z_to_bv 64 0x1a620.
End FREE.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma NoDup_map_inj_in {A B} (f : A -> B) (l : list A) :
  List.NoDup (map f l) -> forall x y, In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|a l IH]; intros ND x y Hx Hy E; [destruct Hx|].
  cbn [map] in ND. inversion ND; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; assumption].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma filter_ext_in {A} (P1 P2 : A -> Prop) `{forall x, Decision (P1 x)} `{forall x, Decision (P2 x)} (l : list A) :
  (forall x, In x l -> (P1 x <-> P2 x)) -> filter P1 l = filter P2 l.
Proof.
  induction l as [|a l IH]; intros HE; [reflexivity|]. rewrite !filter_cons.
  rewrite IH by (intros x Hx; apply HE; right; exact Hx).
  destruct (decide (P1 a)) as [Y|N]; destruct (decide (P2 a)) as [Y'|N']; try reflexivity; exfalso;
    pose proof (HE a (or_introl eq_refl)); tauto.
Qed.
(* [comment removed for export] *)
