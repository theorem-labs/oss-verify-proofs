(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafe STree Malloc Prog.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc4listhc4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~k24mledhc3nilhc4Nonek29BPUntriedk25mkLed79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~q64cptrk26ld_brkk29ld_brkregk27ld_livek28ld_metask27ld_resvk29ld_groupshc6optionk29brk_phasehc3fsthc3apphc4pairq6bround_up_pghc3snd37Corelib5Lists7ListDefhm73mapq64PGSZhc4cons46Stdlib6ZArith6BinInt1Zhp33addhp33subhc4boolhc4andbk27lrangesq6dalloc_ceilingq6branges_freehp33lebhp33ltbq68MAP_ANONq6bMAP_PRIVATEq69MAP_FIXEDhp33pow37Corelib4Init5Logicii94Trueii95Falseq62evii92eqii93andii92exii92ork29brk_quiethp33mulq69PROT_NONEq67PROT_RW36Stdlib5Lists4Listip52Inhp32lthc4Somek27BPGuardk26BPLivek29BPQueriedk27LEN_MAXk24MAPFk25MAPFXq64aptrq6cundef_reasonhp32lehp33eqbhc5falsehc4negbhc3orbk2dlbrk_pages_okq6dbrk_answer_okq6ebrk0_answer_okq6emmap_answer_okq6h4mmap_fixed_answer_okq6h2mprotect_answer_okq6h0munmap_answer_okhp34landk2aset_brkregk29set_brkphk2aset_groupsk29set_metask26BPDeadk29bump_metak28g_removeq66ENOSYSq65TWO64q66is_err04Npos35stdpp9bitvectorbdefinitionski92bvki97Z_to_bvk22wzki9bbv_unsignedk23ehik23elok26pwdisj" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive brk_phase : Type :=
| BPUntried                 (* [comment removed for export] *)
| BPQueried (cur : Z)       (* [comment removed for export] *)
| BPGuard (cur : Z)         (* [comment removed for export] *)
| BPLive                    (* [comment removed for export] *)
| BPDead.                   (* [comment removed for export] *)

Record mled : Type := mkLed {
  ld_resv : list (Z * Z);          (* [comment removed for export] *)
  ld_groups : list (Z * Z);        (* [comment removed for export] *)
  ld_metas : list (Z * Z * Z);     (* [comment removed for export] *)
  ld_brkreg : option (Z * Z);      (* [comment removed for export] *)
  ld_brk : brk_phase;
  ld_live : list cptr              (* [comment removed for export] *)
}.

Definition led_init : ltac2:(zQ "40!h9!j4!jb!ne>4resv@1$1@2$2$0$0$3") := ltac2:(zQ "80!h9!jb!o5!ob!j4!p2!pe!u4\4resv@1$4@2$1$0$0@6$6^1@1$2@2$1$0$0@1$2@2$1@2$1$0$0$0@1$3@2$1$0$0$5@1$2$7").
Definition set_groups : ltac2:(zQ "40!h9!ne!j4!jb>1v@1$2@2$3$0$0>1L$1$1") := ltac2:(zQ "a0!h9!j4!jb!ub!v4!hg0!hga!hh5!pe!ne\1v@1$1@2$2$0$0\1L$9@6$8@1$7^1^2@1$6^1@1$4^1@1$3^1@1$5^1").
Definition set_metas : ltac2:(zQ "40!h9!jb!ne!j4>1v@1$3@2$1@2$1$0$0$0>1L$2$2") := ltac2:(zQ "a0!h9!jb!j4!ub!v4!hhf!hg0!hh5!pe!ne\1v@1$2@2$1@2$1$0$0$0\1L$9@6$8@1$7^1@1$5^1^2@1$4^1@1$3^1@1$6^1").
Definition set_brkreg : ltac2:(zQ "40!h9!ne!hib!jb>1v@1$2@2$3$0$0>1L$1$1") := ltac2:(zQ "a0!h9!hib!jb!ub!hhf!hg0!hga!hh5!pe!ne\1v@1$1@2$2$0$0\1L$9@6$8@1$7^1@1$4^1@1$6^1^2@1$3^1@1$5^1").
Definition set_brkph : ltac2:(zQ "20!ne!hj4>1v$1>1L$0$0") := ltac2:(zQ "80!hj4!v4!hhf!hg0!hga!hh5!pe!ne\1v$0\1L$7@6$6@1$5^1@1$2^1@1$4^1@1$1^1^2@1$3^1").
Definition set_live : ltac2:(zQ "30!ne!j4!u4>1v@1$1$2>1L$0$0") := ltac2:(zQ "90!j4!ub!v4!hhf!hga!hh5!pe!ne!u4\1v@1$0$8\1L$7@6$6@1$5^1@1$3^1@1$4^1@1$2^1@1$1^1^2").

(* [comment removed for export] *)
Definition lranges : ltac2:(zQ "40!h9!j4!jb!ne>1L$3@1$1@2$2$0$0") := ltac2:(zQ "h40!h9!jb!hk0!hk6!hkc!hl3!j4!o5!hib!hm1!hne!ho5!hoc!v4!hhf!hga!hh5!ne!hqb!hr2\1L$h1@3$3@2$1$0$0@1$h0^1@3$3@2$1$0$0@4$a@2$1$0$0@2$1$0$0\1g@2$1$0$0@4$4$0$0@3$2$0$0^1@1$5@3$9$0$0^1@1$e^1@3$3@2$1$0$0@4$a@2$1@2$1$0$0$0@2$1$0$0\1m@2$1@2$1$0$0$0@4$4$0$0@3$2$0$0@3$2@2$1$0$0$0^1@1$5@3$9$0$0@3$2@2$1$0$0$0^1@1$f^1M8\1x@1$8@2$1$0$0@1$6@2$1$0$0@1$d^1\1p@2$1$0$0M1\1p@2$1$0$0@1$6@2$1$0$0^1\1b$0\1l$0@3$c@2$1$0$0@4$4$0$0@2$h2^2$b@2$h3@1$5^1$b@1$7@2$1$0$0@1$7@2$1$0$0").

(* [comment removed for export] *)
Definition lbrk_pages_ok : ltac2:(zQ "30!h9!hr9!ne>1L$2>2lo$0>3len$0$1") := ltac2:(zQ "90!hs0!h9!hs7!ne!ht1!hu1!hqb!huf!hv6\1L$3\2lo$1\3len$1@2$0@2$0@2$8Z^2@2$7@2$6^2^1$4@3$5@1$2^3^2^1").

Definition MAPF : ltac2:(zQ "10!h9$0") := ltac2:(zQ "30!hvd!ig8!hqb@2$2$1$0").
Definition MAPFX : ltac2:(zQ "10!h9$0") := ltac2:(zQ "40!hqb!hvd!ih6!ig8@2$0@2$0$3$1$2").
Definition LEN_MAX : ltac2:(zQ "10!h9$0") := ltac2:(zQ "10!ii2@2$0+2+jf").   (* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint g_remove (a : Z) (l : list (Z * Z)) : list (Z * Z) :=
  match l with
  | [] => []
  | y :: l' => if fst y =? a then l' else y :: g_remove a l'
  end.
Definition bump_meta (a : Z) (m : Z * Z * Z) : Z * Z * Z :=
  let '(b, l, k) := m in if b + (1 + k) * PGSZ =? a then (b, l, k + 1) else m.
Fixpoint ap_remove (c : aptr) (l : list aptr) : list aptr :=
  match l with
  | [] => []
  | y :: l' => if aptr_eqb y c then l' else y :: ap_remove c l'
  end.

(* [comment removed for export] *)
Definition brk_quiet : ltac2:(zQ "10!ne>1L$0P") := ltac2:(zQ "60!ijd!ik5!h9!hj4!ub!ne\1L$5M3\1x$3P@1$4^1$0\3cur$2$1\3cur$2$1$0$0").

Definition event_pre : ltac2:(zQ "20!ne!ike>1L$0>1e$1P") := ltac2:(zQ "i40!h9!il3!il9!im0!jb!ho5!hqb!im6!hkc!hj4!ub!hl3!imc!ike!in8!ik5!inf!iob!iq8!iqe!ir4!hib!irb!is5!ise!p2!ita!iu4!iub!v4!hhf!hga!ne!iv3!iva!jg9\1L$i0\1e$dMd\1e$dP^1\3req$0@2$7@2$2@3$1$0^1Z@3$1$9@1$a^3$h9@2$7@2$3$0\3cur$0@2$2@3$1$9@1$a^4@1$h8^1@3$1$0^2@2$6@1$b^1@2$e+2$5@2$3$0\1b$0@2$3$0\1l$0@2$2@3$1$9@1$a^5$h7@2$2@3$1@1$h5@2$4$0$0@1$hd^5@2$h4@2$4$0$0@4$8$0$0^2^1@3$1$0^3@2$6@2$6^2^1$5\1a$0\3len$0\4prot$0\5flags$0@2$7@2$2@1$c^6@2$2@3$1$0^4Z@2$2@3$1$0^1$hb@2$2@2$7@3$1$0^2$h0@3$1$0^2$h1@2$2@2$h3Z^3@2$h3^3$ha@2$3$0\3cur$0@2$2@3$1$9@1$a^7@1$h6^1@2$2@3$1$0^5@1$b^1@2$2@3$1$0^4$5@2$2@3$1$0^3$h0@3$1$0^2$hc\1a$0\3len$0@2$2@1$c^4@2$3$0\1l$0@2$2@3$h2@2$4$0$0@4$8$0$0^3^1@1$he^5@2$7@3$1$0^2^1@3$1$0^2@1$b^1\1a$0\3len$0\4prot$0@2$2@1$c^5@2$2@3$1$0^2$5@2$2@3$1$0^1$h1@2$3$0\1b$0@2$3$0\1l$0@2$3$0\1k$0@2$2@3$h2@2$4@2$4$0$0$0@4$8@2$4$0$0$0@4$8$0$0^3^2^1@1$hf^8@2$2@3$1$0^6@2$6^3@2$e@2$6+1^1$5@2$i3@2$e@2$6+2^1$5@1$b^2\1p$i1\5caddr$0\4hint$0$f\3why$i2$f").

Definition answer_ok : ltac2:(zQ "40!hr9!h9!ne!ike>1L$2>1e$3>1z$1$0") := ltac2:(zQ "he7!h9!hr9!jb!hib!hqb!jgf!jh6!hs0!jhe!ji5!jib!ho5!jjb!v4!ike!hj4!ub!hs7!ne!ih6!iv3!jkb!jlc!jmd!jo5!jpb!hl3!iva!jqf!in8&@2$9@1$8@2$5^5^4@3$a^7@2$4^2^1$b&@2$7@3$c@2$4^2^1^4^5~0&\1l$0~1&\1b$0~2&M2\1p@2$2$0$0$1^1~3&\1p@2$2$0$0~4&M3\1x@1$3@2$2$0$0$1@1$d^4~5$6\1L$h2\1e$e\1z$0Me\1e$e$1^2\3req$0M1\0$1$1@2$5^1Z@1$h5^2Mf\1x$f$1@1$h0^4~6\3cur$0@2$7@3$c^1^2^3@2$9@1$8@2$5^3^2@3$a^5@1$ha^1@2$hd+2$b\3cur$0M3\1x@1$3@2$2$0$0$1@1$d^5\1p@2$2$0$0M2\1p@2$2$0$0$1^1\1b$0\1l$0@2$7@3$c@2$4^2^1^5^6@2$9@1$8@2$5^6^5@3$a^8@2$4^2^1$b$6~6~6\1a$0\3len$0\4prot$0\5flags$0M1\0$1$1@2$5@2$hc^1$h3Z@3$h6@1$h1^7^3^5@2$h7^4^5\4addr$0\3len$0@1$h9^3\4addr$0\3len$0\4prot$0@1$h8^4\1p$h4\5caddr$0\4hint$0$6\3why$hb$6").

Definition event_post : ltac2:(zQ "30!ne!h9!ike>1L$0>1e$2>1z$1$0") := ltac2:(zQ "i77!h9!jb!ne!hr9!hib!hkc!jgf!ir4!jr7!ho5!v4!js4!hqb!ike!hoc!hj4!hhf!hga!jt0!jtd!ji5!hne!ju9!irb!is5!ise!jv2!jve!ub!kg9!ih6!inf!kh2!iv3!kha!iva!jqf!in8!hr2&@2$7@2$1$0$0@4$5$0$0^2@2$c^1$9&@2$8~0^7&\1l$0~1&\1b$0~2&M1\1p@2$1$0$0$2^1~3&\1p@2$1$0$0~4&M4\1x@1$4@2$1$0$0$2@1$a^4~5^4\1L$2\1e$d\1z$0Md\1e$d$2^2\3req$0M3\0$3$2@2$6^1Z@2$b@1$h9^2^4M3\0$3$2@2$6^2^1Mf\1x$f$2@1$hc^4~6\3cur$0@2$b@1$h7^1^5\3cur$0M4\1x@1$4@2$1$0$0$2@1$a^5\1p@2$1$0$0M1\1p@2$1$0$0$2^1\1b$0\1l$0@2$8~0^8^5~6~6@2$b$h6^4\1a$0\3len$0\4prot$0\5flags$0M3\0$3$2@2$6@2$i4^1$heZM3\0$3$2@1$i2^5^7M3\0$3$2@2$6^2$hf@2$h3@3$e@2$1@2$1$0$0$0@4$5@2$1$0$0$0@4$5$0$0^5^3Z@1$h1^7^7@2$h2@3$e@2$1$0$0@4$5$0$0^5^3@1$h0^7^7@2$b$h8@2$8@2$7@2$1$0$0@4$5$0$0^4@2$i5+2$9^7\1a$0\3len$0@2$h2@2$hb^2@1$h0^5^5\1a$0\3len$0\4prot$0M3\0$3$2@2$h4@2$6^4Z@2$6^4@2$i6$i0$hd@2$h3@4$h5@2$1@2$1$0$0$0@2$1@2$1$0$0$0@1$ha^3@1$h1^6^6^6\1p$i1\5caddr$0\4hint$0^6\3why$i3^4").

(* [comment removed for export] *)
Fixpoint ctree_ok {R} (L : mled) (t : stree ev Z R) (Post : mled -> R -> Prop) : Prop :=
  match t with
  | SRet r => Post L r
  | SVis e k => event_pre L e /\ forall z, answer_ok L e z = true -> ctree_ok (event_post L e z) (k z) Post
  end.

(* [comment removed for export] *)
Inductive cpath {R} : mled -> stree ev Z R -> mled -> R -> Prop :=
| cpath_ret L r : cpath L (SRet r) L r
| cpath_vis L e k z L' r :
    answer_ok L e z = true -> cpath (event_post L e z) (k z) L' r -> cpath L (SVis e k) L' r.

(* [comment removed for export] *)
Inductive creach : mstate -> mled -> Prop :=
| creach_init secret resv : 0 <= secret < 2^64 -> creach (strip (minit secret resv)) (led_init resv)   (* [comment removed for export] *)
| creach_malloc cs L n L' cs' r :
    creach cs L -> 0 <= n -> cpath L (cmalloc cs n) L' (cs', r) ->
    creach cs' (match r with Some c => set_live (c :: ld_live L') L' | None => L' end)
| creach_free cs L c L' cs' :
    creach cs L -> In c (ld_live L) -> cpath L (cfree cs (Some c)) L' cs' ->
    creach cs' (set_live (ap_remove c (ld_live L')) L').

(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition wz : ltac2:(zQ "30!ki3!h9!kk6>1z$1@1$2@1$0#k0") := ltac2:(zQ "30!ki3!h9!kkc\1z$1@2$2@1$0#k0^1").
Definition went : ltac2:(zQ "40!ki3!h9!kk6!jb>1b$1>1n$1@2$3@1$2@1$0#k0@1$2@1$0#k0") := ltac2:(zQ "50!ki3!h9!kl7!kk6!hkc\1b$1\1n$1@4$4@1$3@1$0#k0@1$3@1$0#k0@1$2^2@1$2^1").
Definition wwZ : ltac2:(zQ "40!jb!ki3!h9!kk6>1e@2$0@1$3@1$1#k0@1$3@1$1#k0@2$0$2$2") := ltac2:(zQ "80!ki3!kk6!h9!klc!hk0!hkc!jb!hm1\1e@2$6@1$1@1$0#k0@1$1@1$0#k0@4$5$2$2@2$3@1$0#k0@3$4@1$1@1$0#k0@1$1@1$0#k0^1@2$3@1$0#k0@3$7@1$1@1$0#k0@1$1@1$0#k0^1").
Definition elo : ltac2:(zQ "40!ki3!kk6!jb!h9>1e@2$2@1$1@1$0#k0@1$1@1$0#k0$3") := ltac2:(zQ "50!ki3!kk6!hk0!jb!klc\1e@2$3@1$1@1$0#k0@1$1@1$0#k0@2$4@1$0#k0@3$2@1$1@1$0#k0@1$1@1$0#k0^1").
Definition ehi : ltac2:(zQ "40!ki3!kk6!jb!h9>1e@2$2@1$1@1$0#k0@1$1@1$0#k0$3") := ltac2:(zQ "70!ki3!kk6!klc!hk0!jb!hm1!hqb\1e@2$4@1$1@1$0#k0@1$1@1$0#k0@2$6@2$2@1$0#k0@3$3@1$1@1$0#k0@1$1@1$0#k0^1@2$2@1$0#k0@3$5@1$1@1$0#k0@1$1@1$0#k0^1").

(* [comment removed for export] *)
Definition wcov : ltac2:(zQ "50!ki3!h9!kk6!j4!jb>4maps@1$3@2$4@1$2@1$0#k0@1$2@1$0#k0>2lo$1>2hi$1P") := ltac2:(zQ "c1!ki3!kk6!jb!il9!h9!jg9!iqe!j4!im0!kmb!kn1!iq8&@2$2@1$1@1$0#k0@1$1@1$0#k0\4maps@1$7~0\2lo$4\2hi$4>1x$4>0@2$3@2$5^3^1@2$6^1^2@2$8~0\1e~0@2$3@3$b~0^1^6@2$3@2$5@1$a^1^3@2$6^3@1$9^1").

(* [comment removed for export] *)
Definition edisj : ltac2:(zQ "31!ki3!kk6!jb&@2$2@1$1@1$0#k0@1$1@1$0#k0>2e1~0>2e2~0P") := ltac2:(zQ "71!ki3!kk6!jb!kmb!kn1!jg9!im6&@2$2@1$1@1$0#k0@1$1@1$0#k0\2e1~0\2e2~0@2$6@2$5@1$3^2@1$4^1@2$5@1$3^1@1$4^2").
Inductive pwdisj : list (word * word) -> Prop :=
| pwdisj_nil : pwdisj []
| pwdisj_cons e l : (forall e', In e' l -> edisj e e') -> pwdisj l -> pwdisj (e :: l).
Definition vmwf : ltac2:(zQ "40!ki3!kk6!j4!jb>4maps@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0P") := ltac2:(zQ "c1!ki3!kk6!jb!il9!kmb!j4!kn1!kn7!iq8!jg9!iqe!ii2&@2$2@1$1@1$0#k0@1$1@1$0#k0\4maps@1$5~0@2$3>1e~0>0@3$8~0^1^2@2$3@2$a@1$6^2@1$4^2@2$9@1$4^2@2$b+2+k0@1$7^1").

(* [comment removed for export] *)
Definition brk_disj : ltac2:(zQ "20!h9!ne>1L$1>1b$0>1n$0P") := ltac2:(zQ "c0!h9!hqb!jb!jg9!ir4!hib!hkc!il3!im6!v4!ne!ho5\1L$a\1b$0\1n$0>2b0$0>2l0$0>0@3$7@1$5@2$2$0$0@1$9^5@2$4@2$2$0$0@4$6$0$0^2^1@2$8@2$3@2$1^5^4@2$1^3$b@2$3@2$1^3^2^5").

(* [comment removed for export] *)
Record KL (L : mled) (pbrk : Z) (mo : Model) : Prop := mkKL {
  kl_minv : minv mo;
  kl_halt : m_halted mo = None;
  kl_wf : vmwf (vm_maps (m_vmmaps mo));
  kl_resv : ld_resv L = map wwZ (vm_reserved (m_vmmaps mo));
  kl_resv_top : forall e, In e (vm_reserved (m_vmmaps mo)) -> ehi e <= bv_unsigned (vm_start_brk (m_vmmaps mo));
  kl_start : 0 < bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) mod PGSZ = 0
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) <= bv_unsigned (vm_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_start_brk (m_vmmaps mo)) + 4 * PGSZ <= alloc_ceiling;
  kl_groups : forall b l, In (b, l) (ld_groups L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l);
  kl_metas : forall b l k, In (b, l, k) (ld_metas L) ->
      0 < l < LEN_MAX /\ 0 < b /\ b mod PGSZ = 0 /\ b + mmap_len l <= alloc_ceiling
      /\ 0 <= k /\ (1 + k) * PGSZ <= mmap_len l
      /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo)) /\ brk_disj L b (mmap_len l)
      /\ (forall q, 1 + k <= q -> (q + 1) * PGSZ <= mmap_len l ->
            exists e, In e (vm_noaccess (m_vmmaps mo)) /\ elo e <= b + q * PGSZ /\ b + q * PGSZ + PGSZ <= ehi e);
  kl_distinct : List.NoDup (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L));
  kl_brkreg : forall b l, ld_brkreg L = Some (b, l) ->
      0 < b /\ b mod PGSZ = 0 /\ 2 * PGSZ <= l /\ l mod PGSZ = 0 /\ b + l <= alloc_ceiling
      /\ wcov (vm_maps (m_vmmaps mo)) (b + PGSZ) (b + l);
  kl_phase : match ld_brk L with
      | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
      | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
      | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
          /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
          /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= alloc_ceiling
          /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
          /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
          /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
      | BPDead => True
      end }.

(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
