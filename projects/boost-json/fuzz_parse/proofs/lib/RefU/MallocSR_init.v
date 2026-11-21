(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3: statements written out as text, the launch's channel reader. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require RefU0Gc5. (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Ref0Gc. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil HeapSecret.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac ITree Nodes SysStep Exec Decode.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import Prelim Monad MSafeP STree Malloc MallocCtrl Prog KInv MI_Inv AllocTop MmNodes GapGrid KLink KLink2 KLink3.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.RefU Require Import RSegs RMallocRep MallocMF_klink MallocMF MallocMF_init MallocSR.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require KReplay.
Ltac2 kr_t_MallocSR_init () := KReplay.lz_vm "#$JaK47Corelib7Numbers7BinNums8positive02!sK=1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics?!s<23Run9valid_brk!s\O8!s\%sp!tz>Z!u@?!ue,1C56Stdlib6ZArith6BinInt1Z3pow!sC<2leC!v$@;bv_unsigned!t1=subC79OSSVerify6Proofs:boost_json:fuzz_parse3lib8HeapCeil5hceilC13~~~!vXOAsegments_reserved!sdK5State<!s]'_top!uN=ad!uk=6moduloC8!unN4Spec4Prog9!tO'Z!us&!smY7ps_!wq#!v`Q!uz%:!s_#_model!s_Q8with_tid!u'QRefU8MallocSR2KM!u&'!{C'4Init5Logic6eq_ind!v3U8A!t,#Top?!t6$!xL#_range!v?W8m_vmmaps!s]Q9!tI+!u6^>!u6,!xN-!sv]B!sv,!x++!sz%!}nX;!}n$!vy0!snO:!sn#Secret=hs!s-$!srg7!sr&!t`ccanary!t`i!sr%!~C`4ps_m!sh%I!shT6KLink36hreach00!tX`6ps!#;&#!tZZ5!tZ%KLB!tV]!sj&BUD!tT&!#3F09Datatypes4prod00!u`Z5rban!|1&K!t1<list02!t1VKInv8led!~;-I!#5_63an!u:#!#9z:>pow_pos_nonneg!sN<:!sN#!sJ&4!sJ&9micromega9SatDivModCZ_mod!sP&!s{C7div!sU#!#7h73not!#<F<div!sC=mul!sC<=!tm#!ug#bound!sMA!u9#!sMA2l!tr,5!v%$8PreO!s/#1Z;!uU#0_r_ex!sL?!t8#!sL'!xvO3Lib9LiaTuning9zify_don!#3v&!w;<compareK!w;72eq01!zlB1I!sFA0K!y756VarMap1t02I!sD?0!sD6=RingM!s4'7Formula!t587Env!sT#5PExpr!u@#!sIC2!sIE7!v-<6option02!{y65Tauto8B!t}&!sH6:Z!uK+=Z!sT$CheckerI!w`;0C!vZ<4find!t3AC!t30_s!{?#K!#8\b1!#7+Z6!#CN$5m!#@'^!sk'strip!#6iB!#7t#1K!#:VYP!#Bx#!ufYRefU=!ty%MF!#7W#:mminv!#Bw_7MmNodes5!sq$!#:iA!zh'0!#F>Shalt!#M2R:in_sigmask!#FwQin_nofile!s^Q6!s^#et!ttUurandom!t<Uuid!s[Ug!s[S!v-#groupsK!s^P5Creds01!#TH@7Z_to_bv!t&Q7FdEntry01!s^Q6VmMap!tc$!zAP!yb#tdin!s]Q5in_f!#N5Q7mkM!#R&T:!#L|#c!w7#!s_Q<!s_$!z@X!#SF$!{XT;!s]%!|oV!tz%!~2X@!#3J&_!v}+!#:}58!#T^$_r!t'QC!t'+!wL[E!sh1!wUXA!sj1!w^TD!sf2!wgV!u=2!wpXAin_abort_termina!{pRC!tI$!sh_L!u<1!sq_!wZ2t!#6yR7vm_!#ZX#!#NYX4vmwf!#=q%!#Bt&5Lists4!s+#2In!t#Z3elo!#T0[!sg%hi!#T,Z!sg$6pwdisj!#T/&K!#Q+;1!~&T!#^k$_!#b5ZA!sh+!xbY;vm_noac!s;#!v|Z7ld_resv!xi'!tMS!#h[+!#CP93fst!sC=s!#cyV!zo%wen!#g''!t,'!zp%7!s+#Def3map!#9,Qvm_start_brk!#O}?1!#ZfZ8ehi_!u2,!#O5D4!t8]lo_!vD7!#H:2length!#KO;3na!#Re#!|E1Peano2le!#OK7;ZifyClasses;rew_iff_rev!wTQ6vm!wN:!#Si05Psatz!#Ry7!sO86K!#Q-?;!#W#$!w0$!s{8!xt,3K!#SO;G!#UN&3!teD!#Uy'!#UVE5!|=Z9ld!#Hh%!#73U3Lib6Decode8mmap_len!#7z_8brk_disj!slald_metas!#P[7!#W,&x!#Yp,!#:p,5NoDup01!#4J<appI!s_=0!wO^brkreg!#UVA!#Ra&1!#5w[cov!~Y8!v8%9False!#s{X!#<F$!u@%!wC?or!#TpR=vm_live_bytes!#5QZ6ltota!#|T&!#zn;of_nat!t3]coun!#z#W8!u\$mitK!tJZ!#mh#1!#@_=!{^#1!~CT2Nd:and_elimF3!#:@;!#5924!sJF5!sJF8!#5VD3!#9dA5mkrel!zL,!$,450!$,R?1!#dJ;5eKind!#gs<uni!#gs8!se%4kind!#817!#8\03Op203K!t5A!smJ5I!#<_P!#XA%!#52Z3wwZ!~m8!#?31!#r=34Znat5Nat2Z6inj_le!tPU!#e2%4PGSZ!|#3!$2d<3!v@Q9!s7#Input!vCSRefU5RSegs5rsegs!#3=V>stack_max_siz!#XaRbrk_aslr!sf#!saQ9page!tA%!ujT!#gn0@!$3L-_ref!#>?Z!#5]$<!tg+_eq!#@gaCEIL_MIN!smhAX!{n&!#=RYmled!#Qg&!#<I74True!#4y-!sB4!#uM<:!#vP$ison!#to7!#G2:0!#5R<bool!t\4!sF31!|zQ!#f7'0!ux85!#@N#00K!#@LY!#Ul%!#p/i<ref_!$<Q&!syiE!$=H3!|?[!t&5B!$<;'!u'2!#Ol@1!#MPM!#:AI!#SO[7PGSZ!~UY!xt,7LEN!}dd9brk_pha!zL#!#4~`6BUDCAP!ska8RESV!uK,!smU7GapGrid6GRID_J!sm%".
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshf2bv79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU5RSegs~~~~~~k15rsegs01Z37Corelib4Init5Logico92eq3h5LinuxProcessSemanticsfLinuxProcessSem3Runq2h1segments_reservedq29valid_brkq28valid_sp3h5LinuxProcessSemanticsfLinuxProcessSem5Stateva9ProcInputvaainit_modelvaestack_max_sizeva8with_tid69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8HeapCeil~~~~~~hld5hceil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4RefU8MallocSR~~~~~~hq12KM79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4Prog~~~~~~hu77ps_inithu79reservedZ46Stdlib6ZArith6BinInt1Zijb2leijb3powijb3subhfbbv_unsigned" s.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section HC.
Context {HCEIL : HeapCeil} {HSEC : HeapSecret}.

Theorem KM_init : forall tid brk mbase sp lim inp,
  valid_brk rsegs brk -> valid_sp sp -> 2^34 <= lim ->
  bv_unsigned sp - stack_max_size = hceil ->
  (* LPS 727298f3 port: the launch's channel reader, which the relation now carries
     ([Run.valid_input] gives it through [Run.valid_input_channel_reader]) *)
  in_channel_reader inp = true ->
  KM (ps_init (reservedZ rsegs)) (with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
(* LPS 727298f3 port: written out (rule 11g), restated with the reader premise.  The replay
   built [KLB] with its old fields; at the revision [init_model]'s reserved ledger is the
   image's segments FOLLOWED BY the launch's vDSO/vvar pair ([State.vm_reserved_init_model]),
   which [kb_resv_top]'s [exists V] covers.  Bullets follow boost-beast/http_request's
   Ref/MallocSR_init.v [KM_init]; the [kb_resv_top] witness is openssl/pem's
   (Spec/LB_Init.v [QI_init]). *)
Proof.
  intros tid brk mbase sp lim inp (Hb1 & Hb2 & Hb3) (Hs1 & Hs2 & Hs3) Hlim Hc Hrd.
  set (mo := with_tid tid (init_model (segments_reserved rsegs) brk mbase sp lim inp)).
  rewrite reserved_top_ref in Hb1, Hb2.
  pose proof (hceil_range : 0x7fff7f800000 <= hceil <= 0x7fffff800000) as Hcr.
  assert (Hat : alloc_top (m_vmmaps mo) = hceil) by exact Hc.
  assert (Hsb : bv_unsigned (vm_start_brk (m_vmmaps mo)) = bv_unsigned brk) by reflexivity.
  assert (Hbb : bv_unsigned (vm_brk (m_vmmaps mo)) = bv_unsigned brk) by reflexivity.
  assert (Hlm : vm_limit (m_vmmaps mo) = lim) by reflexivity.
  assert (Hmaps : vm_maps (m_vmmaps mo) = []) by reflexivity.
  assert (Hnacc : vm_noaccess (m_vmmaps mo) = []) by reflexivity.
  assert (Hres : vm_reserved (m_vmmaps mo)
                 = segments_reserved rsegs ++ vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo)))
    by exact (vm_reserved_init_model _ _ _ _ _ _).
  assert (Htop : vdso_top (m_vmmaps mo)
                 = page_round_down_Z (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size)))
    by exact (vdso_top_init_model _ _ _ _ _ _).
  pose proof (vdso_len_bounds (in_kernel inp)) as Lb.
  assert (Ht64 : vdso_top (m_vmmaps mo) < two_pow_64).
  { rewrite Htop. pose proof (page_round_down_Z_le (Z.min (bv_unsigned mbase) (bv_unsigned sp - stack_max_size))) as Pd.
    pose proof (bv_unsigned_in_range 64 sp) as Rs. unfold bv_modulus in Rs.
    unfold two_pow_64, stack_max_size in *. lia. }
  (* each entry of the pair is non-empty and no longer than the pair *)
  assert (Hvd : forall a n, In (a, n) (vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo))) ->
            0 < bv_unsigned n /\ bv_unsigned n <= 20 * 4096).
  { intros a n Hin.
    destruct (vdso_reserved_above _ _ _ _ Ht64 Hin) as [A1 A2].
    pose proof (vdso_reserved_nonzero _ _ _ _ Ht64 Hin) as A3.
    unfold page_size in *. lia. }
  exists (led_init (rband hceil :: reservedZ rsegs)). split; [|split].
  - exact (hreach_init hsecret _ hsecret_range).
  - assert (Elt : ltotal (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    assert (Elc : lcount (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    constructor.
    + exact (mminv_init tid brk mbase sp lim inp).
    + reflexivity.
    + rewrite Hmaps. split; [intros e [] | constructor].
    + rewrite Hnacc. intros e [].
    + exists (segments_reserved rsegs), (vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo))).
      split; [exact Hres|]. cbn [ld_resv led_init]. rewrite Hat. reflexivity.
    + rewrite Hat. unfold CEIL_MIN, CEIL_MAX. lia.
    + exact Hat.
    + exists (vdso_reserved (in_kernel inp) (vdso_top (m_vmmaps mo))).
      split; [|split].
      * unfold vdso_reserved; cbv zeta; destruct (_ <? _)%Z; cbn [length]; lia.
      * pose proof (vdso_text_pages_pos (in_kernel inp)) as HPP.
        pose proof (vdso_text_pages_le (in_kernel inp)) as HL.
        unfold vdso_reserved, vdso_len, vdso_vvar_pages, page_size in *; cbv zeta.
        destruct (_ <? 4096)%Z; cbn [live_bytes]; [lia|].
        rewrite !Z_to_bv_unsigned, !bv_wrap_small by (change (bv_modulus 64) with (2^64)%Z; lia). lia.
      * intros e He. rewrite Hres in He. apply in_app_or in He as [He|He]; [left| right; exact He].
        rewrite Hsb. set (Bb := bv_unsigned brk) in *. clearbody Bb.
        rewrite segments_reserved_ref in He. unfold ref_segments in He.
        cbn [map fst snd] in He. destruct He as [<-|[<-|[<-|[<-|[]]]]];
          unfold ehi, went, wz; cbn [fst snd]; vm_compute bv_unsigned; lia.
    + intros e He. rewrite Hres in He. apply in_app_or in He as [He|He].
      * rewrite segments_reserved_ref in He. unfold ref_segments in He.
        cbn [map fst snd] in He. destruct He as [<-|[<-|[<-|[<-|[]]]]];
          unfold elo, ehi, went, wz; cbn [fst snd]; vm_compute bv_unsigned; lia.
      * destruct e as [a n]. destruct (Hvd a n He) as (V2 & V3).
        unfold elo, ehi. cbn [fst snd]. lia.
    + rewrite Hres, segments_reserved_ref. unfold ref_segments. cbn [map app length].
      unfold vdso_reserved. cbv zeta. destruct (_ <? _)%Z; cbn [length]; lia.
    + try rewrite Hsb; try rewrite Hbb; try rewrite Hat. unfold PGSZ, page_size, brk_aslr_max in *. repeat split; lia.
    + intros b l [].
    + intros b l k [].
    + constructor.
    + intros b l E. discriminate E.
    + cbn [ld_brk led_init]. split; reflexivity.
    + rewrite Elt. reflexivity.
    + rewrite Elc, Hmaps. reflexivity.
    + rewrite Hlm. unfold BUDCAP. lia.
    + intros x Hx. rewrite Hres. apply in_or_app. right. exact Hx.
    + rewrite Hmaps. intros r _ e [].
    + exact Hrd.
  - assert (Elt : ltotal (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    assert (Elc : lcount (led_init (rband hceil :: reservedZ rsegs)) = 0) by reflexivity.
    unfold BUD. rewrite Elt, Elc, Hlm. unfold BUDCAP, RESV_MAX, GRID_J. lia.
Qed.

(* [comment removed for export] *)

End HC.
(* [comment removed for export] *)
