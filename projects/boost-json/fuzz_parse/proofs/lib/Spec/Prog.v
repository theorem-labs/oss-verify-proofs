(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Exec ITree Nodes Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad STree Malloc MallocCtrl.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~06PState79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~k46mstate04mkPS06ps_brk05ps_fa05ps_so37Corelib7Numbers7BinNumsq71Z04ps_m46Stdlib6ZArith6BinInt1Zsa3powsa3sub37Corelib4Init9Datatypesue6option79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~hgf4resp09fixed_ansq74Npos35stdpp9bitvectorbdefinitionshm52bvue4listue4produe4Noneue4boolue4Some3h5LinuxProcessSemantics5Riscv7Preludehqb6bv_eqbhm57Z_to_bv3h5LinuxProcessSemanticsfLinuxProcessSem5Statehu6dSyscallEffect79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6Decode~~~~~~ii58errno_ofue4andbue3nathu67MemCopyii58mmap_lenii55no_cc06FxDone06FxKept06FxLostii59range_ansue4trueii56RgDoneii55RgErrii5cdec_mprotectk46ENOSYSsa3eqbk42ev79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec5Monad~~~~~~ive1Mii58mmap_ansive5mbindive4mretive4msys09neg_errnoii57brk_ansue4unit79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~jo25NMmapue3niljo24NBrkive4munrive4mupd0aset_brk_psue4negbii57dec_brkii58dec_brk0ii58dec_mmapii5ddec_mmap_noneii5adec_munmapjo29NMprotectjo27NMunmapk44aptrk4cundef_reasonive4mget0bMAP_FIXED_Z0edec_mmap_fixed0fdec_mprotect_rwsa4landk44cptrq71N35stdpp7numbers1Nkr06eq_dec35stdpp7numbers1Zksb6eq_dec25stdpp9countableku6bN_countableku6bZ_countableku6eprod_countable25stdpp9decidableli7bprod_eq_deck42IBk44UNITk4ec_mmap_counterk48fold_offk4cget_meta_reck4aget_stridek44metak45s_ctxk47s_slotssa3div25stdpp4baselqa6lookup25stdpp4gmapls04gmapls0bgmap_lookup89OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog2HC~~~~~~lu34bptrue3fstk45cfreelu36membed05set_m04bptrue3sndk44concsa3addsa3mulue4pairii59CEIL_BANDue4consue2tt69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~mo85hceil69OSSVerify6Proofsaboost_jsonafuzz_parse3libaHeapSecret~~~~~~msc7hsecretk45minitk45strip05rband3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypenib7Segmenthm5bbv_unsigned37Corelib5Lists7ListDefnna3map3h5LinuxProcessSemanticsfLinuxProcessSem3Runnp8h1segments_reserved" s.
Import ListNotations.
Import ITree.Exc.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Open Scope mspec_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
Record PState := mkPS {
  ps_m   : mstate;        (* [comment removed for export] *)
  ps_brk : Z;             (* [comment removed for export] *)
  ps_fa  : Z * Z;         (* [comment removed for export] *)
  ps_so  : unit           (* [comment removed for export] *)
}.
Definition set_m : ltac2:(zQ "20!jc!o2>1v$1>1s$0$0") := ltac2:(zQ "60!o2!jc!ob!p1!p9!q0\1v$0\1s$1@4$2^2@1$3^1@1$4^1@1$5^1").
Definition set_brk_ps : ltac2:(zQ "20!jc!s0>1v$1>1s$0$0") := ltac2:(zQ "60!s0!jc!ob!p9!s4!q0\1v$0\1s$1@4$2@1$4^1^2@1$3^1@1$5^1").

Local Notation MP := (Monad.M PState).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition neg_errno : ltac2:(zQ "10!s0>1e$0$0") := ltac2:(zQ "30!s0!u2!u8\1e$0@2$2@2$1+2+k0^1").

Definition MAP_FIXED_Z : Z := 16.

(* [comment removed for export] *)
Inductive fixed_ans : Type := FxKept (e : Z) | FxDone | FxLost (e : Z).
Definition dec_mmap_fixed : ltac2:(zQ "40!s0!hg6!hkb!hl3>4addr$0>3len$0>3rsp$2@1$1$3") := ltac2:(zQ "h74!hle!ho2!ho8!hl3!hof!hg6!hp6!hpd!s0!hq4!ht1!htb!ih4!im2!ime!in5!inb!io6!ip2!hkb!ipb!iq3!iqb&@2$4@1$1@1$0#k0@1$2@1$1@1$0#8&@1$2~0&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$2~2\4addr$8\3len$8\3rsp$h3M7\0$7@1$5$3@1$h2^1Mc\3rsp$c@1$5$3^1\1r@1$1@1$0#k0\aeff_writes~1\9eff_zeros~3\aeff_unmaps~3\aeff_copies@1$2$h0\beff_copyins@1$2@2$4@1$1@1$0#k0$fM2\aeff_writes~1@1$5$3^5M2\9eff_zeros~3@1$5$3^4M2\aeff_unmaps~3@1$5$3^3M5\1x@1$5$8@1$5$3@1$d^6\1e$8@2$9$3@1$h5^1@1$6$3\1p~2\1l~3M4\1p~2@1$5$3^2\1a@1$1@1$0#k0\1n@1$1@1$0#k0M2\1l~3@1$5$3^3M7\0$7@1$5$3@2$e@3$a@1$0#k0^2@2$b@1$0#k0^d@3$a@1$0#k0^1@2$b@1$0#k0@1$h1^cM5\1x@1$5$8@1$5$3@1$d^a\1e$8@2$9$3@1$h6^1M7\0$7@1$5$3@3$a@1$0#k0^a@2$b@1$0#k0^d@2$9$3$h4@1$6$3@1$6$3\2p0~2\2l0~3@1$6$3\1p~2\1l~3@1$6$3\1p~0\1l~1@1$6$3@1$6$3").

(* [comment removed for export] *)
Definition dec_mprotect_rw : ltac2:(zQ "40!s0!hg6!ir3!hkb>4addr$0>3len$0>3rsp$3@1$1$2") := ltac2:(zQ "d0!ir3!hg6!hpd!hp6!s0!hq4!is0!is7!it1!ita!hkb!iua!iv3\4addr$4\3len$4\3rsp$aM1\1x@1$1$0@1$1$0@3$9^3^2^1\1r$0M0\1r$0@1$1$0^1\1e$4M2\0$2@1$1$0@2$c^1$b@1$3$0@2$5$0@1$8^1\7changed$2M2\7changed$2@1$1$0^1@2$5$0@1$7$6@1$3$0@1$3$0").

(* [comment removed for export] *)
Section HC.
Context {HC : HeapCeil}.

Definition ev_step : ltac2:(zQ "40!s0!iv9!jjb!jc>1e$1@2$2$3$0") := ltac2:(zQ "i66!s0!jc!jk0!ir3!jkc!hpd!jl5!jld!jm5!jn0!jjb!hl3!jnb!jre!iv9!iv3!js7!hof!jsd!jt5!jtd!p1!ju5!jv1!jv8!kg3!kgf!khb!kic!kja!kk7!kl2!kl9!km8!kn0!knd!kod!kpe&M2\1a$2$0^1\1e$0@1$8^1\1x$0^1&@3$6$1$0~0&\1a$2~1&M3\1a$3$0^1\1e$0@1$8^1\7changed$5Z&@3$6$1$0~3&\1a$3~4\1e$eMe\1e$e@2$a$1$0^1\3req$0M5\0$5@2$a$1$0@2$f^1Z@5$4$1$0$0@4$7$1$0@1$h2Z$h9\1r$0@5$4$1$c$0@2$h4$1@1$h6^1\0$c@3$6$1$0^2@5$4$1$1$0@1$i1$1\1s$1@5$4$1$9$0@4$7$1$9@1$h2^2@2$h8@1$h5^1^2\1a$9M9\1a$9@2$a$1$0^1@5$4$1$c$0@2$h4$1@1$h6^3\0$c@3$6$1$0^4@3$6$1$0@1$h5^2\4addr$0\3len$0\4prot$0\5flags$0M5\0$5@2$a$1$0@1$h7@2$f@2$i5^1$i2Z@5$4$1$b$0@4$7$1$b@4$d^4^3^2^1@2$i3^4^3\1a$b@3$6$1$0Mb\1a$b$0^1\1e$0@1$8^1^5\1e$0@1$8^1M5\0$5@2$a$1$0@2$f^2Z@5$4$1$2$0@4$7$1$2@4$d^4^3^2^1@3$hb?2HC^3@1$h0@2$h1$0$0~2@5$4$1$2$0@4$7$1$2@4$d^4^3^2^1@3$ha?2HC^3@1$h0@2$h1$0$0~2\4addr$0\3len$0@5$4$1$3$0@4$7$1$3@2$he^2^1@2$hc^2^1~5\4addr$0\3len$0\4prot$0@5$4$1$3$0@4$7$1$3@3$hd^3^2^1@2$i4^3^2~5\1p$hf\5caddr$0\4hint$0@2$h3$1$0\3why$i0@2$h3$1$0").

Fixpoint membed {R} (t : stree ev Z R) : MP R :=
  match t with
  | SRet r => mret r
  | SVis e k => z <- ev_step e ;; membed (k z)
  end.

(* [comment removed for export] *)
Definition bptr : ltac2:(zQ "00T") := ltac2:(zQ "30!hof!s0!kq5@2$0$2$1").

Definition fresh_off : ltac2:(zQ "30!s0!kq5!o2>2cs$2>4slot$1>1n$0$0") := ltac2:(zQ "hc0!s0!kl2!hof!kqc!ks1!ktc!hg6!kq5!u8!kv7!lg6!lh5!lj8!lk7!lkc!ll3!lm4!lmf!lne!lob!o2!lp2!lpa!lq4!kpe!lr6!lsc!lt4\2cs$h4\4slot$7\1n$0M6\1x@1$6@2$2$1$0$0@6$h9$7@2$2$1$0@4$ha$1@4$c$3$4$0$5@6$b$3$4$9$0$5$a@2$2$1$0@4$hb$1@4$c$3$4$0$5@6$b$3$4$9$0$5$a@2$2$1$0^2@1$h6^3\1y@2$2$1$0M2\1y@2$2$1$0$0^1\1g$1\3idx$0=2mr$h3@2$h1^6^2@2$h0@2$h8@1$f@1$h5^7+vf@2$h7@2$8@2$8@1$h2^1$d^5$eZ").

Definition raw_malloc (n : Z) : MP (option bptr) :=
  s <- mget ;;
  '(st', p) <- membed (cmalloc (ps_m s) n) ;;
  mupd (set_m st') ;;;
  mret (match p with Some slot => Some (slot, fresh_off st' slot n) | None => None end).
Definition raw_free : ltac2:(zQ "40!jnb!jjb!mi2!jc>1p$2@2$1$3$0") := ltac2:(zQ "f0!jc!o2!jnb!kq5!jkc!hq4!mia!s0!mj0!km8!jtd!mi2!mj8!s4!mk2\1p$b@5$4$0$0$2@1$9$0\1s$0@5$4$0$1$2@2$c$1@2$8@1$d^1@2$5$3@3$6$3$7^2\3st'$1@2$a$0@1$e^1").
End HC.

(* [comment removed for export] *)
Definition ptr_addr : ltac2:(zQ "30!s0!jc!mk9>1s$1>1p$2$0") := ltac2:(zQ "b0!s0!kq5!mia!mkf!lkc!ml5!jc!mk9!s4!mlc!mm2\1s$6\1p$7@2$9@2$5@1$8^2@3$2$1$0^1@2$a$4@3$3$1$0^1").

(* [comment removed for export] *)
Definition rband : ltac2:(zQ "20!s0!hof>4ceil$0@2$1$0$0") := ltac2:(zQ "30!s0!mm8!mmf\4ceil$0@4$1$0$0^1$2").
(* [comment removed for export] *)
Section PSInit.
Context {HC : HeapCeil} {HSEC : HeapSecret}.
Definition ps_init : ltac2:(zQ "40!s0!ho8!hof!jc>8reserved@1$1@2$2$0$0$3") := ltac2:(zQ "c0!s0!hof!mnc!ho8!mm8!mo3!ms3!ng9!nh4!nhc!ob!ni4\8reserved@1$3@2$1$0$0@4$a@1$9@2$8@1$7?4HSEC@3$2@2$1$0$0@1$b@1$6?2HC^1Z@4$4$0$0ZZ$5").
End PSInit.
(* [comment removed for export] *)

Definition reservedZ : ltac2:(zQ "40!ho8!s0!hof!nm0>4segs@1$0$3@1$0@2$2$1$1") := ltac2:(zQ "c1!hle!ho2!s0!hof!nmb!mia!ho8!mm8!mkf!np1!nm0!ns4&@2$3@1$1@1$0#k0@1$1@1$0#k0\4segs@1$6$a@4$9~0@2$3$2$2\1p~0@4$7$2$2@2$4@1$0#k0@3$5@1$1@1$0#k0@1$1@1$0#k0^1@2$4@1$0#k0@3$8@1$1@1$0#k0@1$1@1$0#k0^1@1$b^1").
(* [comment removed for export] *)
