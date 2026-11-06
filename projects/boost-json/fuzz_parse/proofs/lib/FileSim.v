(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import NArith ZArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RelSpec SimInv ExitSim PropExec CatSim CatExec ErrEscape SeqExec StreamExec StreamSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Sem.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "3h5LinuxProcessSemanticsfLinuxProcessSem5State04m_fs37Corelib4Init9Datatypesj44listj44prod37Corelib4Init5Logicla2eq37Corelib7Numbers7BinNumsn34Npos3h5LinuxProcessSemanticsfLinuxProcessSem2Fsp32Fs07FdEntry05Model08with_fds35stdpp9bitvectorbdefinitionstd2bv05m_fdsj43nilj46optionj44Nonej44Somej43natla1I3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticshidh3Build_machine_statehiddmachine_state3h5LinuxProcessSemanticsfLinuxProcessSem3Runhodh0advance_past_svchodcapply_effect07MemCopy09mkEffectU3h5LinuxProcessSemantics5Riscv7Preludehv25bvmap69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~ii16fp_csrii17fp_regsii14mkstii16regupdii16v_additd2BVtd4BvWf3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypeip97Segmenthod9sys_input08in_sysnohid6ms_gpr06in_arghidcms_read_byte06in_memhidh0ms_writable_byte07in_wmemp34pathj44boolj45falsela3notp38path_eqbj44consj44pair09fd_lookupj43fstj44negbhv26bv_eqb36Stdlib5Lists4Listjof6filter09fd_insert09fd_removej46length3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasejsbbword_to_nat37Corelib4Init3Natkg93subp39file_read46Stdlib5Arith8PeanoNat3Natkie3minii17seg_romj41S79OSSVerify6Proofsaboost_jsonafuzz_parse3lib7FileSim4FPX1~~~~~~klf3mrbii13rdntd6bv_addtd7Z_to_bvj43appkg93add37Corelib4Init5Peanoksc2lt06CstrOk0bcstr_result0dread_cstr_auxjof2Inksc2le09read_cstr0bCstrTooLong37Corelib5Lists7ListDeflie3nthip98PhdrInfohodh1entry_stack_image3h5LinuxProcessSemanticsfLinuxProcessSembStackLayoutlme9EntryDrawlmeh1build_stack_byteslmecstack_to_mem69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~lt5ccat_argv_ptr46Stdlib6ZArith6BinInt1Zmhf3addmhf2ltmhf6of_natmhf3powtdbbv_unsignedn31Z06ENOMEM5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Fs4Openmmfdopenat_errnos" s.

Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma with_fds_fs : ltac2:(zQ "a0!ie!kc!l3!me!oc!re!s3!sc!t3!va>1f@1$1@2$2@1$9@1$4#k0$6>1m$7@3$3$5@1$0@2$8^2^1@1$0^1").
Proof. reflexivity. Qed.
Lemma with_fds_fds : ltac2:(zQ "90!kc!l3!oc!s3!va!me!sc!vf!t3>1f@1$0@2$1@1$4@1$2#k0$3>1m$6@3$5@1$0@2$1@1$4@1$2#k0$3@1$7@2$8^2^1^2").
Proof. reflexivity. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma adv_eff_ret : ltac2:(zQ "h93!oc!va!hg6!l3!hgc!hh5!hhc!kc!hi3!hi9!me!hm4!hnc!hr9!hse!hte!hu7!ih8!ilc!im6!in1!in9!io3!iod!ip2&>0@1$1@1$0#k0@1$4@1$1@1$0#8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$2~1>4regs@2$h1@1$0#5@1$1@1$0#k0>2pc@1$1@1$0#k0>2x8@1$1@1$0#k0>3mem~0>3rom~0>1r@1$1@1$0#k0@3$a$c@1$d@2$e@8$b^6@1$h3?2fx^5@2$6@1$1@1$0#k0^4@1$5@1$1@1$0#k0@1$h2?2fx^3^2@6$h0^1@1$2@2$3@1$1@1$0#k0@1$7@1$1@1$0#8~2~2@1$2$f@1$2@2$3@1$1@1$0#k0$8@5$h4?2fx@3$h5^6@3$h7@1$0#5+aKv$9@2$h8@1$0#5+a^1@2$h6^5+4^3^2").
Proof.
  intros regs pc x8 mem rom r.
  unfold advance_past_svc, apply_effect, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota zeta.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom
       eff_ret eff_writes eff_zeros apply_writes apply_zeros].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma in_sysno_si : ltac2:(zQ "80!oc!va!kc!me!ise!hnc!it9!iu6>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@1$7@3$6^3^2^1^1").
Proof. reflexivity. Qed.
Lemma in_arg0_si : ltac2:(zQ "90!oc!va!kc!me!ise!hnc!iv0!it9!iva>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N0@2$6^2N0").
Proof. reflexivity. Qed.
Lemma in_arg1_si : ltac2:(zQ "90!oc!va!kc!me!ise!hnc!iv0!it9!iva>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N1@2$6^2N1").
Proof. reflexivity. Qed.
Lemma in_arg2_si : ltac2:(zQ "90!oc!va!kc!me!ise!hnc!iv0!it9!iva>4segs@1$2$4>2ms$5>2x8@1$1@1$0#k0@3$3@1$1@1$0#k0@2$8@3$7^3^2^1N2@2$6^2N2").
Proof. reflexivity. Qed.
Lemma in_mem_si : ltac2:(zQ "a0!oc!va!kc!hgc!me!ise!hnc!jg2!it9!jh2>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4>0@1$1@1$0#k0@1$3@1$1@1$0#8@1$9@3$8^3^2^1@1$7^2").
Proof. reflexivity. Qed.
Lemma in_wmem_si : ltac2:(zQ "a0!oc!va!kc!hgc!me!ise!hnc!jha!it9!jif>4segs@1$2$5>2ms$6>2x8@1$1@1$0#k0@3$4>0@1$1@1$0#k0@1$3@1$1@1$0#8@1$9@3$8^3^2^1@2$7^3^2").
Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma path_eqb_neq : ltac2:(zQ "60!jj8!me!jjf!jk6!jke!jl4>1p$0>1q$0>0@1$4@3$1$0^2^1@3$1$2@2$5^3^2$3").
Proof.
  intros p q Hne. destruct (path_eqb p q) eqn:E; [|reflexivity].
  apply path_eqb_eq in E. congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma fd_lookup_cons_eq : ltac2:(zQ "b0!s3!oc!va!l3!hhc!jlf!kc!hgc!jm6!me!jmd>3fds@1$6@2$3@1$2@1$1#k0$0>2fd@1$2@1$1#k0>1e$0@3$9@1$7$0@2$a@3$5@2$3@1$2@1$1#k0$0@4$8@1$2@1$1#k0$0^2^1^3^2@2$4$0^1").
Proof. intros. cbn. rewrite bv_eqb_refl. reflexivity. Qed.

Lemma fd_lookup_cons_neq : ltac2:(zQ "b0!oc!va!s3!l3!me!jmd!jlf!kc!hgc!jm6!jke>3fds@1$7@2$3@1$1@1$0#k0$2>1k@1$1@1$0#k0>1e$2>2fd@1$1@1$0#k0>0@1$a@3$4@1$1@1$0#k0^3^1@3$4@1$8$2@2$5@3$6@2$3@1$1@1$0#k0$2@4$9@1$1@1$0#k0$2^4^3^5^2@2$5^5^2").
Proof.
  intros fds k e fd Hne. cbn.
  rewrite (bv_eqb_neq k fd Hne). reflexivity.
Qed.

Lemma fd_lookup_filter_neq : ltac2:(zQ "d0!oc!va!s3!l3!me!jmd!jn8!kc!jne!hgc!jke!jo5!jq2>3fds@1$7@2$3@1$1@1$0#k0$2>2fd@1$1@1$0#k0>3fd'@1$1@1$0#k0>0@1$a@3$4@1$1@1$0#k0^1^2@3$4@1$9$2@2$5@3$c@2$3@1$1@1$0#k0$2\1p@2$3@1$1@1$0#k0$2@1$8@3$b@1$0#k0@3$6@1$1@1$0#k0$2^1^4^4^2@2$5^4^2").
Proof.
  induction fds as [|[k e] fds IH]; intros fd fd' Hne; [reflexivity|].
  cbn [List.filter fst].
  destruct (bv_eqb k fd) eqn:Hk.
  - apply bv_eqb_eq in Hk. subst k.
    cbn [negb]. rewrite IH by exact Hne. cbn [fd_lookup].
    rewrite bv_eqb_neq by congruence. reflexivity.
  - cbn [negb fd_lookup]. destruct (bv_eqb k fd'); [reflexivity | apply IH; exact Hne].
Qed.

Lemma fd_lookup_insert_eq : ltac2:(zQ "a0!s3!oc!va!hhc!kc!hgc!l3!me!jqc!jmd>3fds@1$4@2$6@1$2@1$1#k0$0>2fd@1$2@1$1#k0>1e$0@3$7@1$5$0@2$9@3$8^3^2^1^2@2$3$0^1").
Proof. intros. unfold fd_insert. apply fd_lookup_cons_eq. Qed.

Lemma fd_lookup_insert_neq : ltac2:(zQ "a0!oc!va!s3!me!jmd!kc!hgc!l3!jke!jqc>3fds@1$5@2$7@1$1@1$0#k0$2>2fd@1$1@1$0#k0>1e$2>3fd'@1$1@1$0#k0>0@1$8@3$3@1$1@1$0#k0^1^3@3$3@1$6$2@2$4@3$9^5^4^3^2@2$4^5^2").
Proof.
  intros fds fd e fd' Hne. unfold fd_insert.
  rewrite fd_lookup_cons_neq by congruence.
  apply fd_lookup_filter_neq. exact Hne.
Qed.

Lemma fd_lookup_remove_neq : ltac2:(zQ "a0!oc!va!me!s3!jmd!kc!hgc!l3!jke!jr7>3fds@1$5@2$7@1$1@1$0#k0$3>2fd@1$1@1$0#k0>3fd'@1$1@1$0#k0>0@1$8@3$2@1$1@1$0#k0^1^2@3$2@1$6$3@2$4@2$9^4^3^2@2$4^4^2").
Proof. intros. unfold fd_remove. apply fd_lookup_filter_neq. assumption. Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma length_file_read : ltac2:(zQ "a0!oc!va!js2!jva!kc!hi3!me!khb!ki2!kk9>4data@1$4@1$1@1$0#8>3off@1$1@1$0#k0>5count@1$1@1$0#k0@3$6$5@2$2@1$1@1$0#8@3$8^3^2^1@2$9@1$3^1@2$7@2$2@1$1@1$0#8^3@1$3^2").
Proof.
  intros data off count. rewrite file_read_unguarded.
  rewrite length_firstn, length_skipn. reflexivity.
Qed.

(* [comment removed for export] *)

Lemma firstn_add {A} : forall (l : list A) n m,
  firstn (n + m) l = firstn n l ++ firstn m (skipn n l).
Proof.
  induction l as [|x l IH]; intros n m.
  - rewrite !firstn_nil, skipn_nil, firstn_nil. reflexivity.
  - destruct n as [|n]; [reflexivity|].
    cbn [firstn skipn Nat.add app]. rewrite IH. reflexivity.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition mrb : ltac2:(zQ "51!oc!va!hgc!kc!ise&>0@1$1@1$0#k0@1$2@1$1@1$0#8>4segs@1$3$4>3mem~0~0") := ltac2:(zQ "70!oc!va!hgc!hhc!kc!ise!kl0\4segs@1$4$5\3mem>0@1$1@1$0#k0@1$2@1$1@1$0#8\1a@1$1@1$0#k0M2\1x@1$2@1$1@1$0#8@1$2@1$1@1$0#8@1^2^1\1b@1$1@1$0#8@2$3@1$1@1$0#8^1@2$6^3^1").

(* [comment removed for export] *)
Lemma mrb_first : ltac2:(zQ "c0!oc!va!kc!hgc!hhc!me!klb!jlf!hi3!ise!kpe!kq5>4segs@1$2$9>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1n$8>1b@1$1@1$0#8>4rest@1$2@1$1@1$0#8>0@3$5@1$3@1$2@1$1@1$0#8@4$b^6^5^4@1$6^3@2$4@1$2@1$1@1$0#8@3$7@1$1@1$0#8^2^1@3$5@1$3@1$1@1$0#8@3$a^7^6^5@2$4@1$1@1$0#8^3").
Proof.
  intros segs mem a n b rest H. unfold mrb. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; congruence.
Qed.

(* [comment removed for export] *)
Lemma rdn_tail : ltac2:(zQ "f0!oc!va!kc!hgc!hhc!me!kq5!klb!jlf!hi3!hi9!ise!iod!ip2!kqc>4segs@1$2$b>3mem>0@1$1@1$0#k0@1$3@1$1@1$0#8>1a@1$1@1$0#k0>1n$9>1b@1$1@1$0#8>4rest@1$2@1$1@1$0#8>0@3$5@1$3@1$2@1$1@1$0#8@4$6^6^5^4@1$7^3@2$4@1$2@1$1@1$0#8@3$8@1$1@1$0#8^2^1@3$5@1$3@1$2@1$1@1$0#8@4$6^7^6@3$e@1$0#k0^5@3$c@1$0#k0+1Kv$a@2$d@1$0#k0+1^4@2$4@1$2@1$1@1$0#8^2").
Proof.
  intros segs mem a n b rest H. cbn [rdn] in H.
  destruct (match mem a with Some b0 => Some b0 | None => seg_rom segs a end)
    as [b1|]; [|discriminate].
  destruct (rdn segs mem (a + 1) n) as [rest1|]; [|discriminate].
  injection H; intros; subst; reflexivity.
Qed.

Lemma read_cstr_aux_of_rdn : ltac2:(zQ "h60!oc!va!kc!js2!hgc!me!kr5!hhc!krf!jlf!hi3!hg6!jke!ks5!ku0!ise!ku6!kue!kvb!kpe!kq5!lga>4segs@1$2$f>3str@1$2@1$1@1$0#8>4fuel$a>3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>0@2$e@2$3@1$1@1$0#8^4^3>0@1$c@3$h5@1$1@1$0#8@2$6@1$0#8Z^5>0@3$5@1$4@1$2@1$1@1$0#8@4$h4^7^4^3@2$d@2$3@1$1@1$0#8^6N1@2$7@1$2@1$1@1$0#8@3$8@1$1@1$0#8^6@3$9@1$1@1$0#8@2$6@1$0#8Z@1$b@1$1@1$0#8@3$5$h1@3$h2@2$h3^8^5^4^6@1$h0^7").
Proof.
  intros segs str; induction str as [|b str IH]; intros fuel mem a Hf Hnz Hr.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    assert (Hb0 : mrb segs mem a = Some (Z_to_bv 8 0))
      by (apply (mrb_first segs mem a 0 (Z_to_bv 8 0) []); exact Hr).
    cbn [read_cstr_aux]. rewrite Hb0. reflexivity.
  - cbn [length] in *. destruct fuel as [|fuel]; [lia|].
    cbn [read_cstr_aux]. cbn [app] in Hr.
    assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
    assert (Hfirst : mrb segs mem a = Some b)
      by (apply (mrb_first segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    assert (Htail : rdn segs mem (a + 1) (length str + 1)
                    = Some (str ++ [Z_to_bv 8 0]))
      by (apply (rdn_tail segs mem a (length str + 1) b (str ++ [Z_to_bv 8 0]));
          exact Hr).
    rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
    rewrite (IH fuel mem (a + 1) ltac:(lia)
               ltac:(intro; apply Hnz; right; assumption) Htail).
    reflexivity.
Qed.

Lemma read_cstr_of_rdn : ltac2:(zQ "h50!oc!va!kc!js2!hgc!me!kr5!hhc!krf!jlf!hg6!jke!ks5!lh0!ise!ku6!kue!lh6!kpe!kq5!lga>4segs@1$2$e>3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>3str@1$2@1$1@1$0#8>0@2$d@2$3@1$1@1$0#8^1Nvvf>0@1$b@3$h4@1$1@1$0#8@2$6@1$0#8Z^2>0@3$5@1$4@1$2@1$1@1$0#8@4$h3^6^5^4@2$c@2$3@1$1@1$0#8^3N1@2$7@1$2@1$1@1$0#8@3$8@1$1@1$0#8^3@3$9@1$1@1$0#8@2$6@1$0#8Z@1$a@1$1@1$0#8@3$5$h0@2$h1@2$h2^7^6^5@1$f^4").
Proof.
  intros segs mem a str Hlen Hnz Hr.
  unfold read_cstr. apply read_cstr_aux_of_rdn; [|exact Hnz|exact Hr].
  change path_max with 4096%nat. lia.
Qed.

(* [comment removed for export] *)
Lemma read_cstr_aux_toolong_of_rdn : ltac2:(zQ "h10!oc!va!kc!me!hi3!hgc!hhc!js2!jke!ise!li1!kue!kvb!kpe!kq5!lga!kr5>4segs@1$2$9>4fuel$4>2bs@1$2@1$1@1$0#8>3mem>0@1$1@1$0#k0@1$5@1$1@1$0#8>1a@1$1@1$0#k0>0@3$3$4@2$7@1$1@1$0#8^3^4>0@1$8@3$f@1$1@1$0#8@2$h0@1$0#8Z^4>0@3$3@1$5@1$2@1$1@1$0#8@4$e^7^4^3^6@2$6@1$2@1$1@1$0#8^5@3$3$b@3$c@2$d^8^5^4^7$a").
Proof.
  intros segs fuel; induction fuel as [|fuel IH]; intros bs mem a Hlen Hnz Hr;
    [reflexivity|].
  destruct bs as [|b bs]; [cbn in Hlen; lia|].
  cbn [read_cstr_aux].
  assert (Hb : b <> Z_to_bv 8 0) by (intro; apply Hnz; left; auto).
  assert (Hfirst : mrb segs mem a = Some b)
    by (apply (mrb_first segs mem a fuel b bs); exact Hr).
  assert (Htail : rdn segs mem (a + 1) fuel = Some bs)
    by (apply (rdn_tail segs mem a fuel b bs); exact Hr).
  rewrite Hfirst. rewrite (bv_eqb_neq b (Z_to_bv 8 0) Hb).
  rewrite (IH bs mem (a + 1) ltac:(cbn in Hlen; lia)
             ltac:(intro; apply Hnz; right; assumption) Htail).
  reflexivity.
Qed.

Lemma read_cstr_toolong_of_rdn : ltac2:(zQ "h10!oc!va!kc!me!hgc!hhc!js2!hi3!jke!ise!li1!kue!lh6!kpe!kq5!lga!kr5>4segs@1$2$9>3mem>0@1$1@1$0#k0@1$4@1$1@1$0#8>1a@1$1@1$0#k0>2bs@1$2@1$1@1$0#8>0@3$3$7@2$6@1$1@1$0#8^1Nhgg0>0@1$8@3$f@1$1@1$0#8@2$h0@1$0#8Z^2>0@3$3@1$4@1$2@1$1@1$0#8@4$e^6^5^4Nhgg0@2$5@1$2@1$1@1$0#8^3@3$3$b@2$c@2$d^7^6^5$a").
Proof.
  intros segs mem a bs Hlen Hnz Hr.
  unfold read_cstr. change path_max with 4096%nat.
  eapply read_cstr_aux_toolong_of_rdn; eauto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma read_argv_cstr_k : ltac2:(zQ "hc1!oc!va!kc!js2!hg6!lk5!hhc!krf!jlf!hi3!hgc!me!ks5!ku0!lkc!ise!ll8!lq2!lqf!ls5!mgf!kq5!mj7!mje!mk4!mke!kr5!ml5&@4$5@1$2@1$1@1$0#8^6^8@1$4@1$1@1$0#8>2ph$e>4segs@1$2$f>2sp@1$1@1$0#k0>2av@1$2@1$2@1$1@1$0#8>2ev@1$2@1$2@1$1@1$0#8>1k$9>3uid@1$1@1$0#k0>2hw@1$1@1$0#k0>3rnd$h1>0@2$d^4@2$3@1$2@1$1@1$0#8^6>0@2$h7@2$h6@2$hb@1$0#k0^8@1$h8@2$3@1$1@1$0#8@7$h2^a^8^7^6^4^3^2@2$h9+2+k0@3$b@1$a@1$2@1$1@1$0#8@4$h5^a@2$h3^9@7$h0^b^9^8^7^5^4^3@4$h4^9^8^7^6@2$c@2$3@1$1@1$0#8~0N1@2$6@1$2@1$1@1$0#8@3$7@1$1@1$0#8~0@3$8@1$1@1$0#8@2$ha@1$0#8Z@1$4@1$1@1$0#8").
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    pre (nth k av [] ++ [Z_to_bv 8 0]) post (length (nth k av []) + 1)) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr sp av ev k)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [exact E | | exact Hnw].
  rewrite length_app. cbn [length]. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma ENOMEM_in_openat_errnos : ltac2:(zQ "40!mm3!mm7!mq3!lga@3$3$0$1$2").
Proof. left. reflexivity. Qed.

(* [comment removed for export] *)

End FPX1.
(* [comment removed for export] *)
