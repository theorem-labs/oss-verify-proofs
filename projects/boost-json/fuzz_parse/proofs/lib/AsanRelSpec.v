(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase Fs State Monad Specs.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import RelSpec.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z3h5LinuxProcessSemanticsfLinuxProcessSem5Statehcfpage_round_up_Z46Stdlib6ZArith6BinInt1Zlc2le04Npos35stdpp9bitvectorbdefinitionsnf2bv37Corelib4Init9Datatypesq14bool37Corelib4Init5Logics02eqq15falseq14listq14prodq14truehccmap_containshcbregion_freelc2ltnfbbv_unsignedq13appq13nilhcdSyscallEffect3h5LinuxProcessSemanticsfLinuxProcessSem5Monadhk27outcomeq14consq13natq14pairs03ands02orhk22Okhc7MemCopyhc5eventhc9mkEffectUs02exs03iffhc5ModelhccSyscallInputhc6VmMapshc9alloc_tophc9errno_rethc8m_vmmapshc9page_sizehc7vm_mapshcbvm_reservedhcbwith_vmmaps5h5LinuxProcessSemanticsfLinuxProcessSem3Sys2Mm4Mmapijebmmap_anon_bijebmmap_errnosijeh9mmap_fixed_destroyed_nextijeh5mmap_fixed_noaccess_bijefmmap_fixed_rw_bijeh7mmap_fixed_rw_budget_okijeh2mmap_fixed_rw_nextijeemmap_modeled_bijefmmap_noaccess_bijeh2mmap_off_aligned_bije9mmap_specijeh3with_mmap_destroyedijeh5with_mmap_replacement4h5LinuxProcessSemanticsfLinuxProcessSem3Sys7Syscalljo95w_is069OSSVerify6Proofsaboost_jsonafuzz_parse3lib7RelSpec~~~~~~js6cmmap_err_out36Stdlib5Lists4Listkh02Inlc3addlc6modulonf7Z_to_bvhccmkVmMapsFullhc6vm_brkhcavm_init_sphc8vm_limithccvm_mmap_basehcbvm_noaccesshccvm_start_brkijeh8mmap_noreserve_backed_okijeh1with_mmap_backingijeh9mmap_noreplace_noaccess_bijeh3mmap_noreplace_rw_b" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma arel_page_round_up_Z_ge : ltac2:(zQ "30!h9!ka!n4>1z$0@2$2^1@1$1^1").
Proof.
  intro z. unfold page_round_up_Z, page_size.
  pose proof (Z.div_mod (z + 4096 - 1) 4096 ltac:(lia)) as H.
  pose proof (Z.mod_pos_bound (z + 4096 - 1) 4096 ltac:(lia)).
  lia.
Qed.

(* [comment removed for export] *)
Lemma map_contains_false_of_free : ltac2:(zQ "c0!n9!pc!r9!t4!t9!u1!u8!uf!v6!hg5!hh3!hh8>4maps@1$5@2$6@1$1@1$0#k0@1$1@1$0#k0>4addr@1$1@1$0#k0>1n@1$1@1$0#k0>0@2$aZ@2$b@1$0#k0^1>0@3$3$2@3$9^4^3^2$7@3$3$2@3$8^5^4^3$4").
Proof.
  induction maps as [|[b s] maps IH]; intros addr n Hn Hf; [reflexivity|].
  cbn [region_free] in Hf. apply andb_true_iff in Hf. destruct Hf as [H1 H2].
  unfold map_contains. cbn [existsb fst snd]. fold (map_contains maps addr n).
  rewrite (IH addr n Hn H2). rewrite orb_false_r.
  unfold iv_overlap in H1. apply negb_true_iff in H1.
  apply Bool.not_true_is_false. intros Hc. apply andb_true_iff in Hc. destruct Hc as [C1 C2].
  apply Z.leb_le in C1. apply Z.leb_le in C2.
  apply andb_false_iff in H1. destruct H1 as [D | D]; apply Z.ltb_ge in D; lia.
Qed.

Lemma region_free_app_r : ltac2:(zQ "92!n9!pc!u8!r9!u1!uf!t4!hg5!hi6&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2X1~1>2X2~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$6$3@3$7@3$8~0^4^3^2^1$5@3$6$3@3$7^4^3^2$5").
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [exact H|].
  cbn in H. apply andb_true_iff in H. apply IH. tauto.
Qed.

Lemma region_free_app_l : ltac2:(zQ "92!n9!pc!u8!r9!u1!uf!t4!hg5!hi6&@2$2@1$1@1$0#k0@1$1@1$0#k0&@1$4~0>2X1~1>2X2~1>1a@1$1@1$0#k0>1n@1$1@1$0#k0>0@3$6$3@3$7@3$8~0^4^3^2^1$5@3$6$3@3$7^5^3^2$5").
Proof.
  induction X1 as [|[b s] X1 IH]; intros X2 a n H; [reflexivity|].
  cbn in H |- *. apply andb_true_iff in H. destruct H as [H1 H2]. rewrite H1. cbn. eapply IH; exact H2.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_rw_commit_outcome : ltac2:(zQ "ja4!n9!pc!t4!hic!r9!u8!uf!h9!hj2!t9!hh8!hn0!hnb!u1!ho2!ho8!hof!hp5!hpa!hq0!hqa!hr2!hre!hs3!hs9!ht1!hu0!hu9!hv5!ig1!v6!ka!igc!hg5!ih8!ii2!ij0!in2!io1!ip0!iqe!is8!itb!iv7!jge!ji0!jj3!jka!jl7!jmf!jrd!kg0!ki3!ki9!n4!hh3!kif!kj8&@2$5@1$1@1$0#k0@1$d@1$1@1$0#8&@1$3~0&@2$5@1$1@1$0#k0@1$1@1$0#k0&@1$3~2>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$h9>1m$h8>1o@1$b$8>0@3$2$4@1$ie^4$6>0@3$2$4@1$i5^7$6>0@3$2$4@1$j2^a$9>0@3$2$4@3$ic^a^9^7$9>0@3$2$4@3$id^b^a^8$9>0@3$2$4@3$i8^c^b^9$9>0@3$2$4@3$i9^d^c^a$6=1h$ha@1$hd^9=2nZ$7@1$hf@2$a@1$0#k0^h0=1n@1$1@1$0#k0@2$j9@1$0#k0^1>0@2$j6@2$j5@2$a@1$0#k0^h3^2@1$hb^3>0@3$2$7@2$j8@2$a@1$0#k0^h4$i0Z>0@2$j7Z@2$a@1$0#k0^h5>0@3$2$4@3$i1@1$i3^6^h6^4$6>0@3$2$4@3$he@1$i2^7^h7^5$6@2$h7@9$if^h8^h7^h6^h5^h4^h3^h2^h1^h0@2$h1@2$j3^h1^h0@2$h1@2$h0@3$2$4@4$ia^h5^h1^h8^6$6@3$2@1$b$8^h0@4$h2$8@6$h5^h8~1@3$c~2@4$f@1$1@1$0#k0@1$1@1$0#k0^h8^6~3~3@1$3$h3@1$3@2$5@1$1@1$0#k0$e@4$j1^h5^h8^6@2$i4@3$ib^8^h8^6^h1@1$3$h4@2$h6$7\1e$7@2$h0@3$j4$7^1$i6@3$2@1$b$8^h1@4$h2$8@6$h5@1$hc^1~1~3@3$c~2@4$f@1$1@1$0#k0@1$1@1$0#k0^h9^7~3@1$3$h3@1$3@2$5@1$1@1$0#k0$e@4$j0^h9^7@3$i7^9^h9^7^h2@1$3$h4").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf Hmc.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf, Hmc. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right; left. split; [assumption | reflexivity].
    + right; right. eexists; split; [eassumption|reflexivity].
  - intros [(e & He & ->) | [(Hb & ->) | (e & He & ->)]].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right; left. neexists 4. split; [exists tt; split; [exact Hb | reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
    + right; right. neexists 4. split; [exists e; split; [exact He|reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma mmap_fixed_rw_fresh_outcome : ltac2:(zQ "ja3!n9!pc!t4!r9!u8!hic!uf!t9!hh8!hj2!hnb!ho8!h9!hn0!ih8!ii2!hi6!u1!ho2!hof!hs3!hp5!hpa!hq0!hs9!ht1!hu0!hu9!hqa!ig1!hr2!kk2!ka!igc!hg5!kl1!kla!km7!kn2!ko1!kof!ij0!in2!iqe!is8!jge!ji0!kpe!jj3!jka!krb!jrd!kg0!ki9!n4!hh3!kif!kj8&@2$4@1$1@1$0#k0@1$1@1$0#k0&@4$b@1$1@1$0#k0@1$1@1$0#k0^h7^5&@1$5~0>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$h9>1m$h8>1o@1$d$9>0@3$2$3@1$j0^4$6>0@3$2$3@1$ia^7$6>0@3$2$3@1$j3^a$7>0@3$2$3@3$id^a^9^7$7>0@3$2$3@3$ie^b^a^8$7>0@3$2$3@3$ib^c^b^9$7>0@3$2$3@3$ic^d^c^a$6=1h$ha@1$hd^9=2nZ$c@1$i0@2$8@1$0#k0^h0=1n@1$1@1$0#k0@2$j9@1$0#k0^1>0@2$j6@2$j5@2$8@1$0#k0^h3^2@1$hb^3>0@3$2$c@2$j8@2$8@1$0#k0^h4$i1Z>0@2$j7Z@2$8@1$0#k0^h5>0@3$2$3@3$i2@3$h0~0@1$f^6@1$e^6^h6^4$6@2$h4@9$j1^h7^h6^h5^h4^h3^h2^h1^h0^f@2$h5@2$j4^h0^f@2$h3@3$2$3@3$if^h4^h0^6$6@3$2@1$d$9^f@4$h6$9@6$he^h7@1$5@2$4@1$1@1$0#k0@1$h1@1$1@1$0#8@3$a~0~1~2~2@1$5$h7@1$5@2$4@1$1@1$0#k0$h2@4$j2^h4^h7^5@2$i9@8$hf@1$f^7@3$a~0~1@1$e^7@1$i7^7@1$i8^7@1$i3^7@1$i5^7@1$i6^7@1$i4^7^h0@1$5$hc").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (arel_page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. neexists 4. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_fixed_noaccess_fresh_outcome : ltac2:(zQ "j73!n9!pc!t4!u8!r9!hic!uf!hh8!hnb!t9!ho8!hj2!h9!hn0!ih8!ii2!hi6!u1!ho2!hs3!hp5!hpa!hq0!hs9!ht1!hu0!hu9!hqa!ig1!hr2!kk2!ka!igc!hg5!kl1!kla!km7!kn2!ko1!kof!ij0!in2!iqe!jge!ji0!jj3!jka!krb!jrd!kg0!ki9!n4!hh3!kif!kj8&@2$3@1$1@1$0#k0@1$1@1$0#k0&@1$5~0&@4$a@1$1@1$0#k0@1$1@1$0#k0^h6^5>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$h8>1m$h7>1o@1$d$b>0@3$2$4@1$id^4$6>0@3$2$4@1$i9^7$6>0@3$2$4@1$j0^a$9>0@3$2$4@3$ib^a^9^7$9>0@3$2$4@3$ic^b^a^8$9>0@3$2$4@3$ia^c^b^9$6=1h$h9@1$hc^8=2nZ$c@1$hf@2$7@1$0#k0^f=1n@1$1@1$0#k0@2$j6@1$0#k0^1>0@2$j3@2$j2@2$7@1$0#k0^h2^2@1$ha^3>0@3$2$c@2$j5@2$7@1$0#k0^h3$i0Z>0@2$j4Z@2$7@1$0#k0^h4>0@3$2$4@3$i1@3$h0~0@1$f^6@1$e^6^h5^4$6@2$h3@9$ie^h6^h5^h4^h3^h2^h1^h0^f^e@2$h4@2$j1^f^e@3$2@1$d$b^e@4$h5$b@6$hd^h6@1$5@2$3@1$1@1$0#k0@1$h1@1$1@1$0#8~1@3$8~0~2~1@1$5$h6@1$5@2$3@1$1@1$0#k0$h2@4$if^h3^h6^5@2$i8@8$he@1$f^7@3$8~0~2@1$e^7@3$8~0~2@1$i6^7@1$i7^7@1$i2^7@1$i4^7@1$i5^7@1$i3^7^f@1$5$hb").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  assert (HnZ : (0 < page_round_up_Z (bv_unsigned len))%Z).
  { pose proof (arel_page_round_up_Z_ge (bv_unsigned len)). pose proof (word_unsigned_range len).
    assert (bv_unsigned len <> 0%Z).
    { intros E. unfold w_is0, bv_eqb in Hlen. rewrite E in Hlen. cbn in Hlen. discriminate. }
    lia. }
  assert (Hn : (0 < bv_unsigned (Z_to_bv 64 (page_round_up_Z (bv_unsigned len))))%Z).
  { rewrite Z_to_bv_unsigned, bv_wrap_small; [exact HnZ|].
    change (bv_modulus 64) with (2^64)%Z. unfold two_pow_64 in *. lia. }
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (region_free_app_l _ _ _ _ Hrf) as Hrfr.
  pose proof (map_contains_false_of_free _ _ _ Hn Hrfm) as Hmc.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrfr, Hmc, Hrf. cbn [andb]. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. neexists 4. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma mmap_noreplace_rw_fresh_outcome : ltac2:(zQ "jc3!n9!pc!t4!r9!u8!t9!hic!uf!hh8!hj2!hnb!ho8!h9!hn0!ih8!ii2!hi6!u1!ho2!hof!hs3!hp5!hpa!hq0!hs9!ht1!hu0!hu9!hqa!ig1!hr2!kk2!ka!igc!hg5!kl1!kla!km7!kn2!ko1!kof!ij0!in2!iqe!is8!jge!ji0!kt1!kuf!kpe!jj3!jka!krb!jrd!kg0!ki9!n4!hh3!kif!kj8&@2$4@1$1@1$0#k0@1$1@1$0#k0&@4$b@1$1@1$0#k0@1$1@1$0#k0^h9^5&@1$6~0>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$h9>1m$h8>1o@1$d$9>0@3$2$3@1$j2^4$7>0@3$2$3@1$ia^7$7>0@3$2$3@1$j5^a$5>0@3$2$3@3$id^a^9^7$5>0@3$2$3@3$ie^b^a^8$5>0@3$2$3@3$ib^c^b^9$5>0@3$2$3@3$ic^d^c^a$5>0@3$2$3@3$if^e^d^b$5>0@3$2$3@3$j0^f^e^c$7=1h$ha@1$hd^b=2nZ$c@1$i0@2$8@1$0#k0^h2=1n@1$1@1$0#k0@2$jb@1$0#k0^1>0@2$j8@2$j7@2$8@1$0#k0^h5^2@1$hb^3>0@3$2$c@2$ja@2$8@1$0#k0^h6$i1Z>0@2$j9Z@2$8@1$0#k0^h7>0@3$2$3@3$i2@3$h0~0@1$f^6@1$e^6^h8^4$7@2$h4@9$j3^h9^h8^h7^h6^h5^h4^h3^h2^h1@2$h5@2$j6^h2^h1@2$h3@3$2$3@3$j1^h6^h2^6$7@3$2@1$d$9^h1@4$h6$9@6$he^h9@1$6@2$4@1$1@1$0#k0@1$h1@1$1@1$0#8@3$a~0~1~2~2@1$6$h7@1$6@2$4@1$1@1$0#k0$h2@4$j4^h6^h9^5@2$i9@8$hf@1$f^7@3$a~0~1@1$e^7@1$i7^7@1$i8^7@1$i3^7@1$i5^7@1$i6^7@1$i4^7^h2@1$6$hc").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna Hnrw. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna, Hnrw. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. split; [assumption | reflexivity].
  - intros [(e & He & ->) | (Hb & ->)].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. neexists 4. split; [exists addr; split; [split; [reflexivity | exact Hb] | reflexivity]|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.

Lemma mmap_noreplace_noaccess_fresh_outcome : ltac2:(zQ "j93!n9!pc!t4!r9!u8!hic!t9!uf!hh8!hnb!ho8!hj2!h9!hn0!ih8!ii2!hi6!u1!ho2!hs3!hp5!hpa!hq0!hs9!ht1!hu0!hu9!hqa!ig1!hr2!kk2!ka!igc!hg5!kl1!kla!km7!kn2!ko1!kof!ij0!in2!iqe!is8!jge!ji0!kt1!jj3!jka!krb!jrd!kg0!ki9!n4!hh3!kif!kj8&@2$4@1$1@1$0#k0@1$1@1$0#k0&@1$5~0&@4$a@1$1@1$0#k0@1$1@1$0#k0^h8^5>4addr@1$1@1$0#k0>3len@1$1@1$0#k0>4prot@1$1@1$0#k0>5flags@1$1@1$0#k0>2fd@1$1@1$0#k0>3off@1$1@1$0#k0>1i$h8>1m$h7>1o@1$d$b>0@3$2$3@1$if^4$7>0@3$2$3@1$i9^7$7>0@3$2$3@1$j2^a$6>0@3$2$3@3$ic^a^9^7$6>0@3$2$3@3$id^b^a^8$6>0@3$2$3@3$ia^c^b^9$6>0@3$2$3@3$ib^d^c^a$6>0@3$2$3@3$ie^e^d^b$7=1h$h9@1$hc^a=2nZ$c@1$hf@2$8@1$0#k0^h1=1n@1$1@1$0#k0@2$j8@1$0#k0^1>0@2$j5@2$j4@2$8@1$0#k0^h4^2@1$ha^3>0@3$2$c@2$j7@2$8@1$0#k0^h5$i0Z>0@2$j6Z@2$8@1$0#k0^h6>0@3$2$3@3$i1@3$h0~0@1$f^6@1$e^6^h7^4$7@2$h3@9$j0^h8^h7^h6^h5^h4^h3^h2^h1^h0@2$h4@2$j3^h1^h0@3$2@1$d$b^h0@4$h5$b@6$hd^h8@1$5@2$4@1$1@1$0#k0@1$h1@1$1@1$0#8~1@3$9~0~2~1@1$5$h6@1$5@2$4@1$1@1$0#k0$h2@4$j1^h5^h8^5@2$i8@8$he@1$f^7@3$9~0~2@1$e^7@3$9~0~2@1$i6^7@1$i7^7@1$i2^7@1$i4^7@1$i5^7@1$i3^7^h1@1$5$hb").
Proof.
  intros addr len prot flags fd off i m o Hoff Hanon Hlen Hmod Hna Hfna Hfrw Hnna. cbv zeta.
  intros Hce Hal Hpos Hrf.
  pose proof (word_unsigned_range addr) as Har.
  pose proof (alloc_top_lt (m_vmmaps m)) as Htop.
  unfold mmap_spec. rewrite Hoff, Hanon, Hlen, Hmod, Hna, Hfna, Hfrw, Hnna. cbn [negb]. cbv zeta.
  assert (E1 : (two_pow_64 <=? bv_unsigned addr + page_round_up_Z (bv_unsigned len))%Z = false).
  { apply Z.leb_gt. unfold two_pow_64 in *. lia. }
  rewrite E1. rewrite bind_get_model. cbv beta zeta.
  rewrite (proj2 (Z.leb_le _ _) Hce), (proj2 (Z.eqb_eq _ _) Hal), (proj2 (Z.ltb_lt _ _) Hpos).
  cbn [negb]. rewrite Hrf. unfold mmap_err_out. sys_unfold.
  split.
  - destruct o as [x m' evs|]; intros H; inv_sys.
    + left. eexists; split; [eassumption|reflexivity].
    + right. reflexivity.
  - intros [(e & He & ->) | ->].
    + left. neexists 4. split; [exists e; split; [exact He|reflexivity]|]. split; reflexivity.
    + right. neexists 4. split; [exists addr; split; reflexivity|].
      split; [|reflexivity]. neexists 4. repeat split; reflexivity.
Qed.
