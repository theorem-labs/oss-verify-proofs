(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Agent Require Import MallocKit_B3 F_ntf_F.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib4Init9Datatypes04bool37Corelib7Numbers7BinNumshe1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~jb4aptrjb6mstate04andbjb3bitjbcget_meta_recjb7m_availjb7m_freedjbam_last_idxjb9mask_uptojb4metajbcokay_to_free46Stdlib6ZArith6BinInt1Zu73addu73eqbu73lorhe4Npos3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshh8dmachine_state3h5LinuxProcessSemantics5Riscv7Preludehm05bvmap35stdpp9bitvectorbdefinitionshof2bv04None37Corelib4Init5Logichr82eq79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentaF_syscalls~~~~~~ht25asegs79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~ihe2MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~im17seg_romhof7Z_to_bvhr82exhr83andjbbm_sizeclassjb4conc79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5AgentdF_malloc_free~~~~~~it83sxv89OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7F_ntf_H4POST~~~~~~ji52AT79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent7F_ntf_H~~~~~~jn08ntf_cond79OSSVerify6Proofsaboost_jsonafuzz_parse3lib5Agent9MallocRep~~~~~~jrc2wz79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~kg43mkRu73powhofbbv_unsignedhr82orjb4optr04truejrc3CTXjb6m_next04Some05falsejb6activeu72lthr83notjrc2pwjrc9meta_wordu72le06option04cons79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~ks74cell04list03nil04prod04pairjn0bentry_casesjrc4mrepks72C8ks72CBkg45munchkg43stkkg45wmono79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~lle7mem_inv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~lq38rw_cellsu73sub04negbu73lebu73ltbu73mul03orbjb4UNITjbaget_stridejbbis_bouncingjbam_freeablejb8m_maplenjb8optr_eqbjbasize_classjb5usage" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition ntf_cond : ltac2:(zQ "40!h8!j7!n9!o0>2st$3>1g$2>1i$1$0") := ltac2:(zQ "f0!o9!j7!n9!of!p5!q4!qe!r8!s5!t1!o0!t8!vf!hg5!hgb\2st$a\1g$2\1i$1=2mr$9@2$4^3^2@2$0@2$d@2$c@2$e@1$6^1@1$5^1@1$3^2@1$8@1$7^1@2$b^4^3").

(* [comment removed for export] *)
Section POST.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (st : mstate) (g : aptr) (i : Z) (m1 : word -> option byte).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation HD := (pw st (active st sc)).
Definition AT : ltac2:(zQ "50!hh1!j7!hkf!ho6!hqc>2pc$1>1R@2$3@1$0#5@1$4@1$0#k0>3ms'$2P") := ltac2:(zQ "b0!hh1!hkf!hqc!hr2!hsc!j7!ho6!ih5!ilb!iq0!iqb\2pc$5\1R@2$6@1$0#5@1$2@1$0#k0\3ms'$1@3$4$1^1@7$8^2?1F@2$a@1$0#k0^3?2fc@1$3@1$2@1$0#k0?2m1@1$9$7").

Definition entry_cases : ltac2:(zQ "10!hkf>3ms'$0P") := ltac2:(zQ "i7i4!hh1!hqc!ir6!iqb!p5!irc!hsc!is3!vf!n9!it1!h8!jhe!jma!jr0!jve!kk0!kk7!kkd!klc!km2!km9!kmf!kn6!knf!ko5!j7!koc!q4!qe!hgb!kp5!hr2!kpa!kq1!hkf!kq7!r8!kr4&@2$he@1$hd@2$4?2st?1g@1$hc@2$4?2st?1g&@3$6$ha~0Z&@2$3@1$0#k0@2$8@2$h2@1$0#k0?2sp-l0&@hf$h0?2ra~2?2gp?2tp^d^c^b?2s0?2s1^a@1$f@1$c@2$h1+2?1i@2$3@1$0#k0@2$a?2st?1g^9^8^7^6^5?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^4^3^2^1&@3$d+hluhc~3^e&\2t6@1$1@1$0#k0~4&@2$2@1$1@1$0#k0~5&\2t5@1$1@1$0#k0~6&@2$2@1$1@1$0#k0~7&\2t4@1$1@1$0#k0~8&@2$2@1$1@1$0#k0~9&\2t3@1$1@1$0#k0~a&@2$2@1$1@1$0#k0~b&\2a7@1$1@1$0#k0~c&@2$2@1$1@1$0#k0~d&\2a6@1$1@1$0#k0~e&@2$2@1$1@1$0#k0~f&\2a5@1$1@1$0#k0~h0&@2$2@1$1@1$0#k0~h1&\2a4@1$1@1$0#k0~h2&@2$2@1$1@1$0#k0~h3&\2a3@1$1@1$0#k0~h4&@2$2@1$1@1$0#k0~h5&\2a0@1$1@1$0#k0~h6&@2$2@1$1@1$0#k0~h7&\2t2@1$1@1$0#k0~h8&@2$2@1$1@1$0#k0~h9&\2t1@1$1@1$0#k0~ha&@2$2@1$1@1$0#k0~hb&\2t0@1$1@1$0#k0~hc&@2$2@1$1@1$0#k0~hd&@2$3@1$0#k0@1$7@2$4?2st?1g&@2$hb?2st@1$7@2$4?2st?1g&@3$6$h4@1$h7@2$4?2st?1g@1$i0$9&@2$3@1$0#k0@2$8@1$7@2$4?2st?1g+a&@2$i2?2st~i0\3ms'$i3@2$h3@2$5@3$6$b@3$e?2st?1g?1i$h9@2$5@1$i1~1~he@2$h3@2$5@3$6$b@3$e?2st?1g?1i$h9@2$5~1@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a4@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@3$d+hltt4@hf$h0?2ra~2?2gp?2tp^c^b^a?2s0?2s1~hf@1$f@1$c@2$h1+2?1i@2$3@1$0#k0@2$a?2st?1g^9^8^7^6^5?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^4^3^2^1^d@2$h3@2$5@3$6$b@3$e?2st?1g?1i$h9@2$5~1@2$5@3$6$h4~i0@2$h8$9?1g~he@2$h3@2$5@3$6$b@3$e?2st?1g?1i$h5@2$5~i1@2$5@2$hf@1$7@2$4?2st?1g+j0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@3$d+hlro0@hf$h0?2ra~2?2gp?2tp^9~hf^8?2s0?2s1~hf@1$f@1$c@2$h1+2?1i@2$3@1$0#k0@2$a?2st?1g^7@2$3@1$0#k0$h6^6^5@2$3@1$0#k0@1$i5@2$4?2st?1g?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^4^3^2^1^a@2$h3@2$5@3$6$b@3$e?2st?1g?1i$h5@2$5~i1@2$5@2$i6+j0@1$7@2$4?2st?1g@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a3@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@3$d+hlrq0@hf$h0?2ra~2?2gp?2tp^9~hf^8?2s0?2s1~hf@1$f@1$c@2$h1+2?1i@2$3@1$0#k0@2$a?2st?1g^7@2$3@1$0#k0$h6^6@2$3@1$0#k0@1$i4@2$4?2st?1g^5?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^4^3^2^1^a@2$h3@2$5@3$6$b@3$e?2st?1g?1i$h5@2$5@3$6$h4@1$h7@2$4?2st?1g@2$h8$9?1g@2$5@2$hf@1$7@2$4?2st?1g+j0@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t5@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@3$d+hlsn0@hf$h0?2ra~2?2gp?2tp^a^9^8?2s0?2s1~i2@1$f@1$c@2$h1+2?1i@2$3@1$0#k0@2$a?2st?1g~i3@2$3@1$0#k0$h6^7^6^5?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^4^3^2^1^b@2$5@3$6$b@3$e?2st?1g?1i$h5@2$5@2$hf@1$7@2$4?2st?1g+j0@2$2$9\2nx$9@2$5@3$6$h4@1$h7@2$4?2st?1g@2$h8$9^1@2$5@1$i1@3$6$9^1?1g@2$2@1$1@1$0#k0\2t0@1$1@1$0#k0@2$2@1$1@1$0#k0\2t1@1$1@1$0#k0@2$2@1$1@1$0#k0\2t2@1$1@1$0#k0@2$2@1$1@1$0#k0\2a5@1$1@1$0#k0@2$2@1$1@1$0#k0\2a6@1$1@1$0#k0@2$2@1$1@1$0#k0\2a7@1$1@1$0#k0@2$2@1$1@1$0#k0\2t3@1$1@1$0#k0@2$2@1$1@1$0#k0\2t4@1$1@1$0#k0@2$2@1$1@1$0#k0\2t6@1$1@1$0#k0@3$d+hlrj8@hf$h0?2ra~2?2gp?2tp^9^8^7?2s0?2s1~i2@1$f@1$c@2$h1+2?1i@2$3@1$0#k0@2$a?2st?1g~i3@2$3@1$0#k0$h6^6^5^4?2s2?2s3?2s4?2s5?2s6?2s7?2s8?2s9?3s10?3s11^3^2@2$3@1$0#k0@2$a?2st^a^1^b").
End POST.

Definition entry_post : ltac2:(zQ "80!hh1!hqc!j7!kr9!hkf!ho6!n9!o0>2ra@1$1@1$0#k0>2sp@1$1@1$0#k0>2gp@1$1@1$0#k0>2tp@1$1@1$0#k0>2s0@1$1@1$0#k0>2s1@1$1@1$0#k0>2s2@1$1@1$0#k0>2s3@1$1@1$0#k0>2s4@1$1@1$0#k0>2s5@1$1@1$0#k0>2s6@1$1@1$0#k0>2s7@1$1@1$0#k0>2s8@1$1@1$0#k0>2s9@1$1@1$0#k0>3s10@1$1@1$0#k0>3s11@1$1@1$0#k0>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>2st$7>1g$6>1i$2>2lo$2>1m>0@1$1@1$0#k0@1$3@1$1@1$0#8>0$4P") := ltac2:(zQ "hd1!hh1!hqc!j7!irc!ih5!kkd!ks1!kr9!lg3!lgb!lh1!lh6!ir6!vf!lhc!hkf!ho6!li2!lj1!lj9!ljf!lk5!lke!ll5!lp8!lte!n9!o0!lua&>0@1$1@1$0#k0@1$7@1$1@1$0#8\2ra@1$1@1$0#k0\2sp@1$1@1$0#k0\2gp@1$1@1$0#k0\2tp@1$1@1$0#k0\2s0@1$1@1$0#k0\2s1@1$1@1$0#k0\2s2@1$1@1$0#k0\2s3@1$1@1$0#k0\2s4@1$1@1$0#k0\2s5@1$1@1$0#k0\2s6@1$1@1$0#k0\2s7@1$1@1$0#k0\2s8@1$1@1$0#k0\2s9@1$1@1$0#k0\3s10@1$1@1$0#k0\3s11@1$1@1$0#k0\1F@2$h0@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\2st$hb\1g$ha\1i$2\2lo$2\1m~0\3ms'$f@2$c~0\2m1~0@2$c@1$9@1$1@1$0#8\4junk@1$9@1$1@1$0#8@2$3@h7$h1^ha^h9^h8^h7^h6^h5^h4^h3^h2^h1^h0^f^e^d^c^b^a^9^8^7^6^2^3@2$3@3$h5@3$6@2$b$2$2@4$e$2$2@2$hc@2$5@1$0#k0^h9+l0@2$5@1$0#k0^h9@1$a@2$b$2$2^4^2@2$3@3$h7$4^4^2@2$3@2$h8$4^2@2$3@4$h6$4^2^5@2$d@2$5@1$0#k0^h9-l0@2$3@4$h9$4^2@2$d@2$5@1$0#k0^h9-l0@3$6$8@2$h4Nk8^1@3$6$8@1$h3^ha@1$a$8@2$h2^8^2").

(* [comment removed for export] *)
Record entry_hyps (st : mstate) (g : aptr) (i : Z) : Prop := mkEH {
  eh_slot : meta_slot st g;
  eh_mw : mw_ok (get_meta_rec st g);
  eh_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  eh_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  eh_i : 0 <= i <= m_last_idx (get_meta_rec st g);
  (* [comment removed for export] *)
  eh_sc : m_sizeclass (get_meta_rec st g) < 48 \/ m_sizeclass (get_meta_rec st g) = 63;
  (* [comment removed for export] *)
  eh_next : forall nx, m_next (get_meta_rec st g) = Some nx -> meta_slot st nx;
  eh_head : forall h, active st (m_sizeclass (get_meta_rec st g)) = Some h -> meta_slot st h;
  eh_ctx : (forall j, 0 <= bounces st j < 256) /\ (m_sizeclass (get_meta_rec st g) < 48 -> 0 <= usage st (m_sizeclass (get_meta_rec st g)) < 2^64);
  (* [comment removed for export] *)
  eh_g50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48;
  eh_g51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48;
  (* [comment removed for export] *)
  eh_g1 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 ->
          m_next (get_meta_rec st g) <> None -> active st (m_sizeclass (get_meta_rec st g)) = Some g
}.

Section ENTRY.
Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : word -> option byte) (st : mstate) (g : aptr) (i lo : Z).
Local Notation mr := (get_meta_rec st g).
Local Notation sc := (m_sizeclass mr).
Local Notation mask := (Z.lor (m_freed mr) (m_avail mr)).
Local Notation maskw := (Z.lor (sxv (m_freed mr)) (sxv (m_avail mr))).
Local Notation sp' := (Z_to_bv 64 (bv_unsigned sp + -80)).
Local Notation G := (Z_to_bv 64 (conc st g)).
Local Notation SELF := (wz (sxv (2 ^ i))).
Local Notation POST := (entry_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i lo m).

Hypothesis EH : entry_hyps st g i.
Hypothesis MI0 : mem_inv asegs m.
Hypothesis LO : alloc_ceiling <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 80.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ntf_cond_unfold : ltac2:(zQ "e0!p5!o9!h8!hsc!jr0!of!q4!qe!r8!s5!t8!vf!hg5!hgb@3$3$2@3$4?2st?1g?1i@2$1@2$c@2$b@2$d@1$7@2$0?2st?1g@1$6@2$0?2st?1g@1$5?1i@1$9@1$8@2$0?2st?1g@2$a?2st?1g").
Proof. reflexivity. Qed.

Lemma okf_unfold : ltac2:(zQ "hb0!h8!p5!km9!is3!ko5!lv0!r8!vf!hg5!lv6!lvc!mg2!knf!o9!mg8!hsc!mgd!n9!mh4!mi1!mif!mjc!kn6!t8!mk7!ml2!mlf@3$f$0@2$h7?2st?1gM0\0$0$0@2$8@1$h4@2$1?2st?1gZ$4M0\0$0$0@2$e@2$9+j0@1$3@2$1?2st?1g@2$a@1$h2@2$1?2st?1g@2$b$h0@1$h9@1$3@2$1?2st?1g$2M0\0$0$0@2$8@1$h5@2$1?2st?1gZ$2M0\0$0$0@1$5@2$h8@1$h6@2$1?2st?1g@2$c$h1?1g$2M0\0$0$0@1$5@2$h3@1$3@2$1?2st?1g?2st$2M0\0$0$0@2$d@2$9@2$b+9@2$7@1$6@2$1?2st?1g+1@2$ha?2st@1$3@2$1?2st?1g@2$a@2$7@1$6@2$1?2st?1g+1+h4$2$4").
Proof. reflexivity. Qed.

End ENTRY.
(* [comment removed for export] *)
