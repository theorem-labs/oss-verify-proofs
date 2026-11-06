(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel ITree Nodes Decode Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_AB.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import Malloc_fp MallocKit_A2.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_A3 ASlot_W1.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~hc9meta_word37Corelib4Init5Logicma2eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~o3bm_set_availo3bm_set_freedo34meta46Stdlib6ZArith6BinInt1Zu43subo36mstate37Corelib4Init9Datatypeshgb4andbhgb4boolo37bounceshgb4negbo3ddecay_bounceso3aset_bounceu43eqbu43lebu43ltb" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)

Lemma meta_word_upd_af : ltac2:(zQ "60!h9!le!ne!s1!sf!td>2mr$5>1a$0>2f'$0@3$2$0@1$1@2$3^2@2$4^1^3@1$1^3").
Proof. intros mr a f'. reflexivity. Qed.

Lemma decay_bounces_eq : ltac2:(zQ "d0!vc!hg2!hi3!hib!hj3!hjd!ne!h9!hk5!hl5!hm2!hm8!hme>2sc$7>2st$1@3$6$1@2$8^2^1M3\0$3$1@2$2@2$2@2$b+7^2@2$c^2+i7@1$5@2$a@2$4^1@2$0^2+7Z@3$9@2$0^2+7@2$0@2$4^1@2$0^2+7+1^1^1").
Proof. intros sc st. reflexivity. Qed.

Section AVZ.
Variables (st : mstate) (m : mem) (g b : aptr) (gh : ghdr).
Let G := conc st g.
Let mr := get_meta_rec st g.
Let f := m_freed mr.
Let ai := g_active_idx gh.
Let act := mask_upto ai.
Let mask := Z.land f act.
Let st4 := upd_meta g (fun r => m_set_avail (Z.land f act) (m_set_freed (Z.ldiff f act) r)) st.
Let st5 := decay_bounces (m_sizeclass mr) st4.
Hypothesis MR : mrep st m.
Hypothesis MSL : meta_slot st g.
Hypothesis AV0 : m_avail mr = 0.
Hypothesis Hmem : m_mem mr = Some b.
Hypothesis Hgh : (s_groups st) !! b = Some gh.
Hypothesis AI : 0 <= ai <= 31.
Hypothesis FR32 : 0 <= f < 2^32.
Hypothesis MW : mw_ok mr.
Hypothesis MASK : mask <> 0.
Hypothesis BNC : forall i, 0 <= bounces st i < 256.
End AVZ.
(* [comment removed for export] *)
