(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocKit_A MallocFacts_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import StoreDj.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~01M04aptr06mstate37Corelib4Init9Datatypeskf4negb37Corelib7Numbers7BinNumsme1Z0eactivate_group0ddecay_bounces0cget_meta_rec05guard0bm_sizeclass06ta_fin46Stdlib6ZArith6BinInt1Zt43eqbkf6optionkf4prodkf4boolkf4Somekf4Nonekf4pair07LActive06active07dequeue07m_avail07m_freed37Corelib4Init5Logichka2eq89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W12TA~~~~~~hm44ta_m06EUndef07UBadPtr02ev06m_next0aset_active09try_avail79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5STree~~~~~~hu44SVis0balloc_group0aalloc_slot0bm_set_avail04meta04optr05queue08upd_metat43sub89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W12AS~~~~~~in26as_grp05ctz32kf1Sin24as_kt43mul0asize_class79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent8ASlot_W1~~~~~~iu59span_exitt43addiu57span_fn79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agenth0F_malloc_enframe~~~~~~jk44zseq36Stdlib5Lists4Listjp67forallbkf4trueiu58span_chkt42lehka3andt42lt" s.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_n8 segs m a bs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section TA.
Context {R : Type}.
Variables (sc : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition ta_avz : ltac2:(zQ "30!je!k1!k7>3st3$2>2m3$1@1$0?1R") := ltac2:(zQ "b0!k7!m7!o7!ob!k1!pb!qa!r8!rf!sc!uc\3st3$0\2m3$4@5$3?1R^1^2\3st4$0\4mask$2@5$7?1R+i8@1$1@2$a^1Z@5$9?1R@2$5@1$8@2$6^2^3^2^3^1?1k?4bail?4bail").

(* [comment removed for export] *)
Definition ta_act (st2 : mstate) (m2 : aptr) (mask : Z) : Malloc.M R :=
  let mr2 := get_meta_rec st2 m2 in
  let gai := match m_mem mr2 with Some _ => group_active_idx st2 (default (0%N,-1) (m_mem mr2)) | None => 0 end in
  let '(st3, m3) :=
    if Z.land mask (mask_upto gai) =? 0 then
      if negb (optr_eqb (m_next mr2) (Some m2)) then
        match m_next mr2 with
        | Some mn => (set_active sc (Some mn) st2, mn)
        | None => (st2, m2)
        end
      else
        let cnt := gai + 2 in
        let size := size_class (m_sizeclass mr2) * UNIT in
        let span := UNIT + size * cnt in
        let cnt := span_loop 300%nat cnt span size in
        let cnt := if m_last_idx mr2 + 1 <? cnt then m_last_idx mr2 + 1 else cnt in
        match m_mem mr2 with
        | Some g => (set_group_active_idx g (cnt - 1) st2, m2)
        | None => (st2, m2)
        end
    else (st2, m2) in
  ta_avz st3 m3.

(* [comment removed for export] *)
Definition ta_m (st1 : mstate) (m1 : aptr) : Malloc.M R :=
  let mask := m_freed (get_meta_rec st1 m1) in
  let '(st2, m2, mask) :=
    let mr := get_meta_rec st1 m1 in
    if (mask =? mask_upto (m_last_idx mr)) && negb (m_freeable mr =? 0) then
      match m_next mr with
      | Some mn => (set_active sc (Some mn) st1, mn, m_freed (get_meta_rec st1 mn))
      | None => (st1, m1, mask)
      end
    else (st1, m1, mask) in
  ta_act st2 m2 mask.

(* [comment removed for export] *)
Lemma try_avail_eq : ltac2:(zQ "hc0!k1!k7!v2!vb!hg2!je!qa!hg9!uc!hh0!hh7!o7!hhe!hi7!hif!hj8!hk1!m7!hle!hq8!hr0!hr8!hs1!hs5!hsd!sc!ht9!ii1>2st$1@3$h2@1$5?1R@5$ha?1R?2sc^1?1k?4bailM2\1x@1$2$0@1$5?1R@2$d^1?2sc\1m$0M4\0$4@1$5?1R@1$h1@2$8@1$f@2$6^2^1Z@5$h9?1R^2^1@1$f@2$6^2^1?1k=5step1@1$2@2$3$1$0M4\0$4@1$2@2$3$1$0@2$8@1$h0@2$6^2^1Z=3st1$1@3$e@1$c?2sc^1^2M2\1x@1$2$0@1$2@2$3$1$0@2$d^1?2sc\2m1$0@2$7@2$3$1$0@4$a$1$0^2^1@1$9@2$3$1$0M2\1x@1$2$0@1$2@2$3$1$0@1$h7@2$6^2^1\2m1$0@2$7@2$3$1$0@4$a$1$0@3$h8?2sc@2$7$0^1^3^1@1$9@2$3$1$0M2\5step1@1$2@2$3$1$0@1$5?1R^1\1p@2$3$1$0M3\1p@2$3$1$0@1$5?1R^1\3st1$1\2m1$0@2$h3^2^1M4\0$4@1$5?1R@2$8@1$h0@2$6^3^2Z@2?1k@3$e@1$c?2sc^2^3Z@5$hb$h6$b?1R@1$h4$h5\0$b?4bail@2?1k^1Z").
Proof. intros st. reflexivity. Qed.
End TA.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section AS.
Context {R : Type}.
Variables (lay : layout_hook) (f : nat) (sc req : Z) (k : mstate -> Z -> Malloc.M R) (bail : Malloc.M R).

(* [comment removed for export] *)
Definition as_grp : ltac2:(zQ "20!je!k7>3st1$1@1$0?1R") := ltac2:(zQ "e0!k7!v2!k1!hhe!je!ii9!ij6!hj8!ik2!ikf!il5!ilb!im2!imc\3st1$0@8$5?1R?3lay@3$6?1R?3lay?1f^1?2sc?3req\3st2$0\2go$aM1\2go@1$1$2@1$4?1R^1\1g$2=3st3$0@3$c^1\1r$9@2$8@2$d@1$7^1+1^1^3@6$b?1R@1$3?2sc^2^1\3st4$0@2?1k^1Z?4bail@2?1k^2-1?4bail").

Definition as_k : ltac2:(zQ "30!o7!je!k7>3st1$2>5first$0@1$1?1R") := ltac2:(zQ "80!hg2!m7!o7!ir6!je!is0!k7!uc\3st1$6\5first$2M0\0$0@1$4?1R@1$1@2$7^1Z@2?1k^2@1$5^1@1$3^2").

Lemma alloc_slot_S : ltac2:(zQ "70!is7!hle!isb!je!ij6!k7!ht9>2st$5@3$1@1$3?1R@8$4?1R?3lay@1$0?1f^1?2sc?3req?1k?4bail@5$6?1R?2sc^1$2?4bail").
Proof. intros st. reflexivity. Qed.
End AS.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint span_exit (fuel : nat) (span size : Z) : bool :=
  match fuel with
  | O => false
  | S f => if Z.lxor span (span + size - 1) <? 4096 then span_exit f (span + size) size else true
  end.

(* [comment removed for export] *)
Definition span_fn : ltac2:(zQ "20!o7!hg2>2sc$0>3cnt$0$1") := ltac2:(zQ "50!it3!o7!it9!ji6!jj3\2sc$1\3cnt$1@3$3Nhic@2$4+h0@2$0@2$0@1$2^2+h0^1@2$0@1$2^2+h0").
Definition span_chk : ltac2:(zQ "20!hg2!o7>2sc$1$0") := ltac2:(zQ "40!o7!jj9!joe!jq9\2sc$0@3$3$0@1$1^1@2$2+2+i0").

Lemma span_chk_true : ltac2:(zQ "70!hg2!jr4!hle!o7!jrb!joe!jq9@3$2$0@3$6$3$4@2$5+1+if$1").
Proof. vm_compute. reflexivity. Qed.

Lemma span_fn_ok : ltac2:(zQ "80!js7!jsc!o7!hg2!jr4!hle!jj9!jt3>2sc$2>3cnt$2>0@2$1@2$0+1^2@2$7^2+j0>0@2$1@2$0+2^2@2$0^2+i1@3$5$3@2$6^4^3$4").
Proof. intros sc cnt.
  intros Hsc Hc.
  pose proof (forallb_zseq span_chk 1 47 sc span_chk_true ltac:(lia) ltac:(lia)) as X. unfold span_chk in X.
  exact (forallb_zseq (span_fn sc) 2 32 cnt X ltac:(lia) ltac:(lia)).
Qed.

Lemma span_exit_ok : ltac2:(zQ "b0!js7!it3!jsc!o7!it9!hg2!jr4!hle!ji6!jj3!jt3>2sc$3>3cnt$3>0@2$2@2$0+1^2@2$a^2+j0>0@2$2@2$0+2^2@2$0^2+i1@3$7$5@3$8Nhic@2$9+h0@2$1@2$1@1$4^4+h0^3@2$1@1$4^4+h0$6").
Proof. intros sc cnt. intros Hsc Hc. exact (span_fn_ok sc cnt Hsc Hc). Qed.
