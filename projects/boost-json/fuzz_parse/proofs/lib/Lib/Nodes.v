(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)


(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import PropExec MState Mem Exec ITree.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsk1dmachine_statek17ms_regs3h5LinuxProcessSemantics5Riscv3Semp27reg_get37Corelib4Init9Datatypesre4list37Corelib4Init5Logictd1Itd2eq3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeva7Segment3h5LinuxProcessSemanticsfLinuxProcessSem3Runhj99sys_input3h5LinuxProcessSemanticsfLinuxProcessSem5Statehn26in_arg79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Nodes~~~~~~hqa4areghf2BVhf4BvWfre4prod79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~ig13le8re3appre3fstre3snd36Stdlib5Lists4Listil48flat_mapig12wahfbbv_unsigned01Zhn2cSyscallInputre4Nonehn27mkInputhf7Z_to_bvre6optionhqa4nodere4consre4Somere3nilhqaapure_inputtd3andk1ems_svc_pendingre6lengthk16ms_mem46Stdlib6ZArith6BinInt1Zjh22lejh26of_natig18bytes_atjh22ltjh23powtd2ork16ms_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~jm17seg_romtd2extd3not37Corelib4Init5Peanojr62le4h5LinuxProcessSemanticsfLinuxProcessSem3Sys4Uapijt09O_CLOEXECjt0bO_LARGEFILEig15wr_athqabiovec_bytesil47Forall2il42Inil46concatjh23addjh25ldiff79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5ITree~~~~~~km04respre3nathn27MemCopyhn29mkEffectUhn29errno_rethqa4eff0hn25Modelhn27FdEntryhn25m_fdshn28alloc_fdhn29fd_inserthn29fd_lookuphn28with_fds5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openli6dopenat_errnoshqa6efferrhn25eventtd5Falsere4bool3h5LinuxProcessSemanticsfLinuxProcessSem2Fslod4path3h5LinuxProcessSemanticsfLinuxProcessSem5Monadls02Okhj9h4spurious_refusal_cfg3h5LinuxProcessSemanticsfLinuxProcessSem5Specsmgdcsyscall_spechqaanode_input69OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Scfg~~~~~~ml98the_scfg37Corelib5Lists7ListDefmpc3map3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasemra8len_wordlod9fs_lookuphn25EBADFhn26ENOENThn26FdFilehn27WriteEvhn24m_fshqabopen_resultlod9file_readlod8path_eqbhn26EISDIRhn2cENAMETOOLONGhn26ENOTTYhn25FdDirhn29SockStatehn29fd_removehn25m_tidhn28path_maxhn28with_tid5h5LinuxProcessSemanticsfLinuxProcessSem3Sys6Kernel4Forkns2h0PID_MAX_ENVELOPE4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Uaccessogfh0delivered_writesjt08dot_path46Stdlib5Arith8PeanoNat3Natom43lebhf6bv_addhn2bwith_haltedhf6bv_andhn29FdChannelhn27FdFileWhn29m_vm_lazyhn26VmMapsre3orbhn27vm_mapsre5falsere4negbre4truehn27map_hashn2fpage_round_up_Zhn29page_sizehn2bregion_freehn2atwo_pow_64hn2bvm_reserved4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Syscallpl45w_is0jh23eqbjh23lebjh26modulohn2cmap_containsre4andbhn2bvm_noaccess5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm8Mprotectpsfh9mprotect_grows_conflict_bpsfh2mprotect_modeled_bhn29alloc_top5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapqk9h5mmap_fixed_noaccess_bqk9emmap_modeled_bqk9fmmap_noaccess_bqk9h1mmap_plain_anon_btd4Truehn28m_vmmapshqabmmap_safe_bhqafmprotect_safe_bhqadmunmap_safe_b" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition areg : ltac2:(zQ "30!h9!jc!n8>2ms$2>1r@1$1@1$0#5@1$1@1$0#k0") := ltac2:(zQ "50!h9!n8!o8!r4!jc\2ms$1\1r@1$4@1$0#5@2$3@1$2^2^1").
Lemma in_a0_si : ltac2:(zQ "c0!h9!jc!t6!v1!v5!hif!n8!hm5!hq0!hu6!hue!hv3>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$8@3$7^3^2^1N0@2$9^2@3$a@1$0#5+aKv$3@2$b@1$0#5+a").
Proof. reflexivity. Qed.
Lemma in_a1_si : ltac2:(zQ "c0!h9!jc!t6!v1!v5!hif!n8!hm5!hq0!hu6!hue!hv3>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$8@3$7^3^2^1N1@2$9^2@3$a@1$0#5+bKv$3@2$b@1$0#5+b").
Proof. reflexivity. Qed.
Lemma in_a2_si : ltac2:(zQ "c0!h9!jc!t6!v1!v5!hif!n8!hm5!hq0!hu6!hue!hv3>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$8@3$7^3^2^1N2@2$9^2@3$a@1$0#5+cKv$3@2$b@1$0#5+c").
Proof. reflexivity. Qed.
Lemma in_a3_si : ltac2:(zQ "c0!h9!jc!t6!v1!v5!hif!n8!hm5!hq0!hu6!hue!hv3>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$8@3$7^3^2^1N3@2$9^2@3$a@1$0#5+dKv$3@2$b@1$0#5+d").
Proof. reflexivity. Qed.
Lemma in_a4_si : ltac2:(zQ "c0!h9!jc!t6!v1!v5!hif!n8!hm5!hq0!hu6!hue!hv3>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$8@3$7^3^2^1N4@2$9^2@3$a@1$0#5+eKv$3@2$b@1$0#5+e").
Proof. reflexivity. Qed.
Lemma in_a5_si : ltac2:(zQ "c0!h9!jc!t6!v1!v5!hif!n8!hm5!hq0!hu6!hue!hv3>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4@1$1@1$0#k0@2$8@3$7^3^2^1N5@2$9^2@3$a@1$0#5+fKv$3@2$b@1$0#5+f").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition iovec_bytes : ltac2:(zQ "40!h9!jc!t6!hva>4iovs@1$2@2$3@1$1@1$0#k0@1$1@1$0#k0@1$2@1$1@1$0#8") := ltac2:(zQ "91!h9!jc!hva!ijb!ik2!ik8!t6!ike!im7&@2$2@1$1@1$0#k0@1$1@1$0#k0\4iovs@1$6~0@4$8~0@1$1@1$0#8\1p~0@3$4@1$1@1$0#8@1$3@3$5@1$1@1$0#k0@1$1@1$0#k0^1@1$3@3$7@1$1@1$0#k0@1$1@1$0#k0^1^1").

(* [comment removed for export] *)

Lemma wa_unsigned_id : ltac2:(zQ "50!h9!jc!v5!in3!in9>1w@1$1@1$0#k0@3$2@1$1@1$0#k0@1$3@2$4@1$0#k0^1^1").
Proof. intros. unfold wa. apply Z_to_bv_bv_unsigned. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive node : Type :=
| NWrite (fd : Z) (bs : list byte)                 (* [comment removed for export] *)
| NWritev (fd : Z) (bufs : list (list byte))       (* [comment removed for export] *)
| NOpen (path : list byte)                         (* [comment removed for export] *)
| NRead (fd : Z) (buf : Z) (count : Z)             (* [comment removed for export] *)
| NClose (fd : Z)                                  (* [comment removed for export] *)
| NIoctl (fd : Z) (req : Z)                        (* [comment removed for export] *)
| NSetTid                                          (* [comment removed for export] *)
| NExit (code : Z)                                 (* [comment removed for export] *)
| NBrk (req : Z)                                   (* [comment removed for export] *)
| NMmap (addr len prot flags : Z)                  (* [comment removed for export] *)
| NMunmap (addr len : Z)                           (* [comment removed for export] *)
| NMprotect (addr len prot : Z).                   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition pure_input : ltac2:(zQ "50!t6!h9!io7!ioa!jc>2no$2>4args@1$0@1$4@1$1#k0$3") := ltac2:(zQ "71!h9!jc!ipa!t6!io7!iq1!iqc&\0@1$1@1$0#k0@1$2@1$1@1$0#8\2no$4\4args@1$3@1$1@1$0#k0@4$5@2$6@1$0#k0^2^1~0~0").

Definition node_input : ltac2:(zQ "30!ir6!ioa!irf>1n$2@1$0$1") := ltac2:(zQ "d2!h9!io7!jc!ioa!is7!iqc!ipa!ise!t6!it5!itb!irf!ir6&@3$4@1$2@1$0#k0@2$5@1$0#k0^1@1$9@1$2@1$0#k0&@3$4@1$2@1$0#k0@2$5@1$0#k0^2~0\1n$bMb\1n$b@1$c$3^1\2fd$1\2bs@1$8@1$2@1$0#8@1$6$3\2fd$1\4bufs@1$8@1$8@1$2@1$0#8@1$6$3\4path@1$8@1$2@1$0#8@1$6$3\2fd$1\3buf$1\5count$1@1$6$3\2fd$1@1$6$3\2fd$1\3req$1@1$6$3@1$6$3\4code$1@1$6$3\3req$1@2$7$3@2$a+t6~0\4addr$1\3len$1\4prot$1\5flags$1@2$7$3@2$a+te@3$4@1$2@1$0#k0@2$5@1$0#k0^4@3$4@1$2@1$0#k0@2$5@1$0#k0^3@3$4@1$2@1$0#k0@2$5@1$0#k0^2@3$4@1$2@1$0#k0@2$5@1$0#k0^1@3$4@1$2@1$0#k0@2$5@1$0#k0-1@3$4@1$2@1$0#k0@2$5@1$0#k0Z@1$9@1$2@1$0#k0\4addr$1\3len$1@2$7$3@2$a+t7~1\4addr$1\3len$1\4prot$1@2$7$3@2$a+u2@3$4@1$2@1$0#k0@2$5@1$0#k0^3~1").

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section AtNode.
Variable segs : ltac2:(zQ "20!t6!hif@1$0$1").

Definition at_node : ltac2:(zQ "20!n8!irf>1n$1>2ms$0P") := ltac2:(zQ "idh7!h9!jc!iu9!v5!iqc!v1!hu6!hue!hv3!io7!ir6!ise!iuf!t6!jg0!jg9!jia!jj0!in9!hva!jja!jk6!jkc!jl3!jl8!irf!jq0!ik2!is7!ik8!it5!ike!jqb!jr0!jsa!n8!kg1!kge!khd!ki6!kj5!kk0!kk6!kl0!kl7&@2$h7@3$3$9^2+1@3$3$9^2+2&@3$7@1$0#5+aKv$5@2$8@1$0#5+a&@2$6^3~1&@3$3@1$1@1$0#k0~2@2$4@1$0#k0^2&@3$7@1$0#5+cKv$5@2$8@1$0#5+c&@2$6^3~4&@2$4@1$0#k0@1$h1@2$e@1$1@1$0#8^1&>0@1$1@1$0#k0@1$a@1$1@1$0#8&@3$3~7@1$h8^3@1$ha?4segs&@3$7@1$0#5+bKv$5@2$8@1$0#5+b&@2$6^3~9&@2$h3@1$1@1$0#k0@1$1@1$0#k0&@1$d~b&@2$6^4~9&@2$6^2~1&@2$6^4~1&@3$3@1$1@1$0#k0~f@2$4@1$0#k0^3&@3$3@1$1@1$0#k0~d@2$4@1$0#k0^2&@2$6^4~4&@3$3@1$1@1$0#k0~h2@2$4@1$0#k0^1&@3$3@1$1@1$0#k0~e@2$4@1$0#k0^1&@3$3@1$1@1$0#k0~a@2$4@1$0#k0^1&@2$2~3~h5\1n$h9\2ms$i3Mh9\1n$h9P^2\2fd$9\2bs@1$d@1$1@1$0#8@2$2@3$3@1$a@1$1@1$0#k0@1$c^3@2$b@1$1@1$0#k0@2$4@1$0#k0+k0@2$2~0@2$2~3@2$2@3$3@1$1@1$0#k0~5~6@2$2@2$h5@1$h1@2$e@1$1@1$0#8^1@2$h6+2+k0@2$2~8@4$h4?4segs@1$f^3@2$h2@1$0#k0~a^1\2fd$9\4bufs@1$d@1$d@1$1@1$0#8@2$2@3$3@1$a@1$1@1$0#k0@1$c^3@2$b@1$1@1$0#k0@2$4@1$0#k0+k2@2$2~0@2$2~3@2$2@3$3@1$1@1$0#k0~5@2$4@1$0#k0@1$h1@2$e@1$d@1$1@1$0#8^1@2$2@2$i2@2$e@1$d@1$1@1$0#8^1Nkg0@2$2@2$h5@1$h1@2$e@1$1@1$0#8@2$ia@1$1@1$0#8^1@2$h6+2+jf@2$2~8@2$i0~c\4iovs~c@2$2@4$h4?4segs@1$f^4@2$h2@1$0#k0~d@1$i7^1@5$i8~b@1$d@1$1@1$0#8\3iov~b\2bs@1$d@1$1@1$0#8@2$2@3$3@1$1@1$0#k0@3$hf@1$1@1$0#k0@1$1@1$0#k0^2~6@4$h4?4segs@1$f^6@2$h2@1$0#k0@3$hd@1$1@1$0#k0@1$1@1$0#k0^2^1^1^2\4path@1$d@1$1@1$0#8@2$2@3$3@1$a@1$1@1$0#k0@1$c^2@2$b@1$1@1$0#k0@2$4@1$0#k0+j8@2$2@3$3@1$1@1$0#k0~e@2$4@1$0#k0-m4@2$2@3$3$9@2$ic@2$h2@1$0#k0@2$6^2~4@2$ib$i4$i5Z@2$2@1$i1@3$i9@1$1@1$0#8@2$4@1$0#8Z^1@2$2@3$3~7@1$h8^2@1$ha?4segs@4$h4?4segs@1$f^2@2$h2@1$0#k0@2$6^2~9@3$hb@1$1@1$0#8^1@3$hc@1$1@1$0#8@2$4@1$0#8Z@1$he@1$1@1$0#8\2fd$9\3buf$9\5count$9@2$2@3$3@1$a@1$1@1$0#k0@1$c^4@2$b@1$1@1$0#k0@2$4@1$0#k0+jf@2$2@2$2@2$h0+3^3@2$h5^3@2$h6+2+i0@2$2~h0@2$2~h1@2$2~h3@2$2@2$h0Z^1@4$i6?4segs@1$f^4^2^1\2fd$9@2$2@3$3@1$a@1$1@1$0#k0@1$c^2@2$b@1$1@1$0#k0@2$4@1$0#k0+j9@2$2@2$2@2$h0+3^1@2$h5^1@2$h6+2+i0~h4\2fd$9\3req$9@2$2@3$3@1$a@1$1@1$0#k0@1$c^3@2$b@1$1@1$0#k0@2$4@1$0#k0+hd@2$2@2$2@2$h0Z^2@2$h0^2+2@2$2@3$3$9^1+lkh3~h6@3$3@1$a@1$1@1$0#k0@1$c^1@2$b@1$1@1$0#k0@2$4@1$0#k0+m0\4code$9@2$2@2$h7@3$3@1$a@1$1@1$0#k0@1$c^2@2$b@1$1@1$0#k0@2$4@1$0#k0+ld@3$3@1$a@1$1@1$0#k0@1$c^2@2$b@1$1@1$0#k0@2$4@1$0#k0+le~h4\3req$9@2$2@3$3@1$a@1$1@1$0#k0@1$c^2@2$b@1$1@1$0#k0@2$4@1$0#k0+t6~h4\4addr$9\3len$9\4prot$9\5flags$9@2$2@3$3@1$a@1$1@1$0#k0@1$c^5@2$b@1$1@1$0#k0@2$4@1$0#k0+te@2$2@3$3@1$1@1$0#k0@2$6^5~1@2$4@1$0#k0^4@2$2@3$3@1$1@1$0#k0@2$6^5~9@2$4@1$0#k0^3@2$2@3$3@1$1@1$0#k0@2$6^5~4@2$4@1$0#k0^2@2$2@3$3@1$1@1$0#k0@2$6^5@3$7@1$0#5+dKv$5@2$8@1$0#5+d@2$4@1$0#k0^1@2$2@3$3@1$1@1$0#k0@2$6^5@3$7@1$0#5+eKv$5@2$8@1$0#5+e@2$4@1$0#k0-1@3$3@1$1@1$0#k0@2$6^5@3$7@1$0#5+fKv$5@2$8@1$0#5+f@2$4@1$0#k0Z\4addr$9\3len$9@2$2@3$3@1$a@1$1@1$0#k0@1$c^3@2$b@1$1@1$0#k0@2$4@1$0#k0+t7~h6\4addr$9\3len$9\4prot$9@2$2@3$3@1$a@1$1@1$0#k0@1$c^4@2$b@1$1@1$0#k0@2$4@1$0#k0+u2@2$2~h0@2$2~h1~h3").

End AtNode.

(* [comment removed for export] *)
Ltac at_node_red :=
  cbn [at_node]; unfold areg; cbn [ms_regs ms_svc_pending ms_rom ms_mem MSsvc MS];
  repeat match goal with
  | |- context [reg_get ?R ?r] =>
      let p := eval vm_compute in (bv_key r) in
      let R' := eval hnf in R in
      change (reg_get R r) with (match tget p R' with Some v => v | None => w0 end);
      cbv beta iota delta [tget]
  end.

Ltac split_spine :=
  lazymatch goal with
  | |- _ /\ _ => split; [|split_spine]
  | |- _ => idtac
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition eff0 : ltac2:(zQ "30!h9!kpc!jc>1r@1$2@1$0#k0$1") := ltac2:(zQ "82!h9!jc!it5!hva!t6!kq4!kqa!kr5&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~0\1r@1$1@1$0#k0@6$7^1@1$2@2$3@1$1@1$0#k0@1$4@1$1@1$0#8~1~1@1$2$6@1$2@2$3@1$1@1$0#k0$5").
Definition efferr : ltac2:(zQ "20!io7!kpc>1e$0$1") := ltac2:(zQ "30!io7!ks2!ksf\1e$0@1$2@1$1^1").

(* [comment removed for export] *)
Definition open_result : ltac2:(zQ "30!kt7!ku0!kpc>2mo$0>3ent$1>3eff$2>3mo'$0P") := ltac2:(zQ "h50!v5!iu9!kt7!io7!ku0!kub!kpc!ipa!ir6!jqb!jl3!h9!kv4!lg0!lgd!lha!lla!ksf!lmb!kk0!jc\2mo$2\3ent$4\3eff$6\3mo'$2@2$a@2$9$3\1e$3@2$1@3$h3$3^1$h0@2$1@3$0$6^3@1$h2^1@3$0$2^2^5=2fd@1$h4@1$b#k0@1$c@1$5^4@2$1@3$0@1$8$4@2$e@1$5^5^1@1$7$4@2$1@3$0$6^3@1$h1^1@3$0$2^2@2$f@3$d@1$5^5^1^4^5").

(* [comment removed for export] *)
Section NStep.
Context {SC : StepCfg}.
Definition nstep : ltac2:(zQ "50!kt7!t6!ln5!kpc!irf>1n$4>2mo$0>3eff$3>3mo'$0>3evs@1$1$2P") := ltac2:(zQ "k33!h9!v5!jc!iu9!t6!ln5!io7!ir6!kpc!kt7!lne!it5!iqc!ioa!lo6!lmb!ku0!jr0!lr8!lue!lv4!mjb!kub!ksf!mkb!mp0!jg0!hva!irf!jk6!mr3!mu9!mv5!ng2!ngb!nh5!nhf!lgd!nia!lha!nj2!kk6!jj0!in9!kq4!jqb!nk1!nke!nla!nm4!nn4!nne!kqa!no7!lg0!np4!nq1!kr5!nqa!nr6!nva!ok3!ol8!onf!jia!jkc!oo6&@2$hb@1$2@1$0#k0@1$2@1$0#k0&@1$b~0&\1p$h2\6offset@1$2@1$0#k0$a\1n$hc\2mo$9\3eff$8\3mo'$9\3evs@1$4$5Mhc\1n$hcP^5\2fd$6\2bs@1$4@1$2@1$0#8@2$3@3$1$8^5@1$h7@2$c@1$0#k0@1$ia@2$ha@1$2@1$0#8^1@2$3@3$1$9^4^6@3$1@1$4$5^3@4$he@1$2@1$0#8$5@1$i4@2$c@1$0#k0^2^1\2fd$6\4bufs@1$4@1$4@1$2@1$0#8@2$3@3$1$8^5@1$h7@2$c@1$0#k0@1$ia@2$ha@1$2@1$0#8@2$i9@1$2@1$0#8^1@2$3@3$1$9^4^6@3$1@1$4$5^3@4$he@1$2@1$0#8$5@1$i4@2$c@1$0#k0^2@2$i9@1$2@1$0#8^1\4path@1$4@1$2@1$0#8@2$3@3$1@1$4$5^2@1$b$5Me\0$eP@2$jf$ja@2$ha@1$2@1$0#8^1@2$3@3$1$8^4@1$f$j1@3$1$9^3^5M4\4path@1$4@1$2@1$0#8P^1@2$3@3$1$8^4@1$f$i2@3$1$9^3^5\1b@1$2@1$0#8\1l@1$4@1$2@1$0#8Me\0$eP@2$if^3$je@4$i8^7$j3^6^5M7\1x@1$7@1$4@1$2@1$0#8P@2$i0@1$i6^7^3\1l@1$4@1$2@1$0#8@4$i8^8@2$i3^4@2$c@1$0#k0Z^7^6@2$3@3$1$8^6@1$f$i2@3$1$9^5^7\2fd$6\3buf$6\5count$6@2$3@3$1@1$4$5^4@1$b$5M7\1x@1$7$h0P@2$i5@1$h6^7@2$c@1$0#k0^3\1f$h0Mh0\1f$h0P^1\4chan@1$2@1$0#k0$a\1p$h2\3off@1$2@1$0#k0M7\1x@1$7@1$4@1$2@1$0#8P@2$i0@1$i6^a^2\4data@1$4@1$2@1$0#8=2bs@1$4@1$2@1$0#8@3$ie^1^2@2$c@1$0#k0^5@2$3@3$1$8^b@6$j9@2$hf@1$2@1$0#8^1@2$jd@2$c@1$0#k0^7^1~1~1@1$b$j4@1$b@2$hb@1$2@1$0#k0$ic@3$1$9^a@2$i7@3$j6@1$h6^c@2$c@1$0#k0^8@2$i3^4@3$k2@1$0#k0^3@2$hf@1$2@1$0#8^1^c$a~2~2~2@2$3@3$1$8^7@1$f$j0@3$1$9^6^8\2sk$j5$a\2id@1$2@1$0#k0\6writer$e$a\2rd$e\2wr$e$a$a@2$3@3$1$8^6@1$f$i1@3$1$9^5^7\2fd$6@2$3@3$1@1$4$5^2@1$b$5@2$3@2$3@2$k0+3^1@2$hd^1@2$k1+2+i0M7\1x@1$7$h0P@2$i5@1$h6^5@2$c@1$0#k0^1\1f$h0@2$3@3$1$8^5@1$h7@2$c@1$0#k0Z@3$1$9^4@2$i7@2$j7@1$h6^6@2$c@1$0#k0^2^6@2$3@3$1$8^4@1$f$i1@3$1$9^3^5\2fd$6\3req$6@2$3@3$1@1$4$5^3@1$b$5@2$3@3$1$8^5@1$f$j2@3$1$9^4^6@2$3@3$1@1$4$5^1@1$b$5@2$id@1$2@1$0#k0\1t@1$2@1$0#k0@2$3@3$1$8^4@1$h7^1M7\1x@1$7@1$2@1$0#k0P@1$j8^5\2t0@1$2@1$0#k0@2$3@3$1@1$2@1$0#k0^2^1@3$1$9^4^6@2$3@2$3@2$hdZ@2$ib@1$0#k0^1@2$hd@2$ib@1$0#k0^1$jc@3$1$9^3@2$jb^1^5\4code$6$a\3req$6@2$3@3$1@1$4$5^2@1$b$5M7\1x@1$7$dP@1$h8^6\1i$d@2$3@3$h5^1^6@4$h3$8^5^4^3@1$h1@4$h4@1$h9?2SC^1^6^5$a\4addr$6\3len$6\4prot$6\5flags$6@2$3@3$1@1$4$5^5@1$b$5M7\1x@1$7$dP@1$h8^9\1i$d@2$3@3$h5^1^9@4$h3$8^8^7^6@1$h1@4$h4@1$h9?2SC^1^9^8$a\4addr$6\3len$6@2$3@3$1@1$4$5^3@1$b$5M7\1x@1$7$dP@1$h8^7\1i$d@2$3@3$h5^1^7@4$h3$8^6^5^4@1$h1@4$h4@1$h9?2SC^1^7^6$a\4addr$6\3len$6\4prot$6@2$3@3$1@1$4$5^4@1$b$5M7\1x@1$7$dP@1$h8^8\1i$d@2$3@3$h5^1^8@4$h3$8^7^6^5@1$h1@4$h4@1$h9?2SC^1^8^7$a").
End NStep.

Definition nexit : ltac2:(zQ "40!kt7!h9!irf!jc>1n$2>2mo$0>4code@1$3@1$1#k0>3mo'$0P") := ltac2:(zQ "c0!io7!lne!h9!jc!t6!kt7!irf!v5!iqc!iu9!oof!ope\1n$6\2mo$5\4code@1$3@1$2#k0\3mo'$5M6\1n$6P^4\2fd$0\2bs@1$4@1$3@1$2#8$1\2fd$0\4bufs@1$4@1$4@1$3@1$2#8$1\4path@1$4@1$3@1$2#8$1\2fd$0\3buf$0\5count$0$1\2fd$0$1\2fd$0\3req$0$1$1\1c$0@2$9@3$7@1$3@1$2#k0^3@3$b@1$2#k0@2$8@1$2#k0^1@2$8@1$2#k0+vf@3$7$5^2@2$a^3^4\3req$0$1\4addr$0\3len$0\4prot$0\5flags$0$1\4addr$0\3len$0$1\4addr$0\3len$0\4prot$0$1").

(* [comment removed for export] *)
Definition minv : ltac2:(zQ "10!kt7>2mo$0P") := ltac2:(zQ "hb1!h9!jc!ku0!v5!ir6!iu9!ise!lgd!kub!iqc!oq7!t6!jk6!in9!hva!jr0!lr8!ipa!it5!mv5!nh5!or4!kt7!nia!nq1!orf!nva&@2$e@1$1@1$0#k0@1$1@1$0#k0\2mo$h6@2$5@3$3@1$b~0@1$h9^1@1$h2~0@2$5@3$3@1$4$2@2$7@1$8^1@2$9@1$0#k0Z@2$6$2@1$a@2$9@1$0#k0Z@2$5@3$3@1$4$2@2$7@1$8^1@2$9@1$0#k0+1@2$6$2@1$a@2$9@1$0#k0+1@2$5@3$3@1$4$2@2$7@1$8^1@2$9@1$0#k0+2@2$6$2@1$a@2$9@1$0#k0+2@2$5>1k@1$1@1$0#k0>1c@1$1@1$0#k0>0@3$3@1$4$2@2$7@1$8^3^2@2$6$2@1$a^1@2$c@2$d@1$0#k0^3+3@2$5>1k@1$1@1$0#k0>1p$h0>3off@1$1@1$0#k0>0@3$3@1$4$2@2$7@1$8^4^3@2$6$2@2$h4^2^1@1$f@3$3@1$4@1$b@1$1@1$0#8@2$h3@1$h7^5^3@1$h1@1$b@1$1@1$0#8@2$5>1k@1$1@1$0#k0>1p$h0>3off@1$1@1$0#k0@1$f@3$3@1$4$2@2$7@1$8^4^3@2$6$2@2$h5^2^1>1t@1$1@1$0#k0>0@3$3@1$4@1$1@1$0#k0@1$h8^2@2$6@1$1@1$0#k0^1@2$5@2$cZ@2$d@1$0#k0^2@2$c@2$d@1$0#k0^2$ha").

(* [comment removed for export] *)
Definition munmap_safe_b : ltac2:(zQ "40!h9!jc!lo6!osc>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>1h$3$2") := ltac2:(zQ "h90!h9!lo6!jc!in9!ot6!otc!ik2!ou7!ouf!hva!ov6!io7!osc!ovd!pg8!phb!pi8!pj7!pk5!po8!kl0!pp1!pp8!ppf!iqc\4addr@1$2@1$0#k0\3len@1$2@1$0#k0\1h$cM1\0$1$1@2$4@1$8@2$h5@2$h7@2$3@1$0#k0^3$fZ@1$h3^2$a=2nZ$b@1$e@2$3@1$0#k0^2M1\0$1$1@2$h6$h1@2$h4@2$3@1$0#k0^4^1$7=1n@1$2@1$0#k0@2$h8@1$0#k0^1@2$4@3$d@1$5^3^5^1@3$h0@3$6@2$9@1$2@1$0#k0@1$2@1$0#k0@1$h2^3@1$5^3^5^1").

Definition mprotect_safe_b : ltac2:(zQ "40!h9!jc!lo6!osc>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>1h$3$2") := ltac2:(zQ "ha0!lo6!h9!ov6!jc!in9!pq9!pr9!pg8!otc!ps0!ou7!ouf!ot6!io7!osc!phb!pi8!pj7!qg7!qi5!po8!kl0!pp1!pp8!ppf!iqc\4addr@1$3@1$1#k0\3len@1$3@1$1#k0\4prot@1$3@1$1#k0\1h$eM0\0$0$0@1$h2^2$2M0\0$0$0@1$b@2$h6@2$h8@2$4@1$1#k0^4$fZ$2M0\0$0$0@1$h4^3$2M0\0$0$0@2$h7$h1@2$h5@2$4@1$1#k0^4@1$7@2$4@1$1#k0^3$2M0\0$0$0@1$h3^2=2nZ$d@1$7@2$4@1$1#k0^3=1n@1$3@1$1#k0@2$h9@1$1#k0^1@2$c@2$6@3$5@1$9^3^6^1@3$5@1$8^3^6^1@2$6@3$5@1$8^3^6^1@3$h0@1$9^3^6^1$a").

(* [comment removed for export] *)
Definition mmap_safe_b : ltac2:(zQ "40!h9!jc!lo6!osc>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1h$3$2") := ltac2:(zQ "hd0!lo6!h9!jc!in9!ou7!ouf!ot6!ov6!kl0!pp8!iqc!pr9!io7!osc!qjc!pq9!pg8!phb!pi8!pj7!otc!pk5!qnd!qp7!qq9!qrc!po8!pp1!ppf\4addr@1$2@1$1#k0\3len@1$2@1$1#k0\4prot@1$2@1$1#k0\5flags@1$2@1$1#k0\2fd@1$2@1$1#k0\3off@1$2@1$1#k0\1h$d@2$6@2$6@3$h7^5^4^2@3$h8^5^4^2M0\0$0$0@1$ha^6@1$h9^4M0\0$0$0@3$h6^5^4^2=2nZ$c@1$h0@2$3@1$1#k0^6M0\0$0$0@2$9$h3@2$8@2$3@1$1#k0^8^1$7M0\0$0$0@1$5@2$9@2$8@2$3@1$1#k0^8^1@1$e^2$4M0\0$0$0@1$5@2$hb@2$hc@2$3@1$1#k0^8$h1Z$7@2$b@3$h2@1$h5^2^8@2$a@1$1#k0^1@3$f@1$h4^2^8@2$a@1$1#k0^1$4").

Definition nsafe : ltac2:(zQ "20!kt7!irf>1n$1>2mo$0P") := ltac2:(zQ "f0!io7!h9!iqc!qt2!t6!lo6!ov6!v5!qt9!irf!jc!kt7!qu5!qv4!rg7\1n$9\2mo$bM9\1n$9P^2\2fd$0\2bs@1$4@1$a@1$1#8$3\2fd$0\4bufs@1$4@1$4@1$a@1$1#8$3\4path@1$4@1$a@1$1#8$3\2fd$0\3buf$0\5count$0$3\2fd$0$3\2fd$0\3req$0$3$3\4code$0$3\3req$0$3\4addr$0\3len$0\4prot$0\5flags$0@3$7$5@7$c@2$2@1$1#k0^4@2$2@1$1#k0^3@2$2@1$1#k0^2@2$2@1$1#k0^1@2$2@1$1#k0-1@2$2@1$1#k0Z@1$8^5$6\4addr$0\3len$0@3$7$5@3$e@2$2@1$1#k0^2@2$2@1$1#k0^1@1$8^3$6\4addr$0\3len$0\4prot$0@3$7$5@4$d@2$2@1$1#k0^3@2$2@1$1#k0^2@2$2@1$1#k0^1@1$8^4$6").

(* [comment removed for export] *)
(* [comment removed for export] *)
