(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Checks Require Import ExecutableSpecs.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Prelim Monad MSafe STree Malloc Prog KInv.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Export KArith.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.

Ltac splits := repeat (lazymatch goal with |- _ /\ _ => split | |- _ => fail end).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_KStep () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.true"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.KInv.elo"; "OSSVerify.KrLib.Heap.KInv.ehi"; "OSSVerify.KrLib.Heap.KInv.vmwf"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.iv_subtract"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.KInv.wcov"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "OSSVerify.KrLib.Lib.ITree.resp"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "OSSVerify.KrLib.Lib.Nodes.nstep"; "OSSVerify.KrLib.Lib.Nodes.NBrk"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_r_ok"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_model_next"; "LinuxProcessSemantics.LinuxProcessSem.State.mkEffectU"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_zeros"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_unmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.MemCopy"; "Corelib.Init.Datatypes.nat"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Mm.Mmap.brk_grow_ok"; "Stdlib.ZArith.BinInt.Z.modulo"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "Corelib.Init.Datatypes.app"; "OSSVerify.KrLib.Heap.Malloc.PGSZ"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "OSSVerify.KrLib.Lib.Nodes.nsafe"; "OSSVerify.KrLib.Lib.Nodes.NMmap"; "OSSVerify.KrLib.Heap.Malloc.PROT_NONE"; "OSSVerify.KrLib.Heap.KInv.MAPFX"; "OSSVerify.KrLib.Heap.KInv.mled"; "OSSVerify.KrLib.Heap.KInv.KL"; "OSSVerify.KrLib.Lib.Nodes.minv"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.State.m_halted"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Heap.KInv.brk_phase"; "phase_inv"; "OSSVerify.KrLib.Heap.KInv.set_brkph"; "OSSVerify.KrLib.Heap.Prog.PState"; "OSSVerify.KrLib.Heap.KInv.frame_ok"; "OSSVerify.KrLib.Heap.KInv.ld_brk"; "OSSVerify.KrLib.Heap.KInv.BPUntried"; "OSSVerify.KrLib.Heap.MSafe.mspec"; "OSSVerify.KrLib.Heap.Prog.ps_brk"; "OSSVerify.KrLib.Heap.Monad.mbind"; "OSSVerify.KrLib.Heap.Monad.msys"; "OSSVerify.KrLib.Lib.Decode.dec_brk0"; "Corelib.Init.Datatypes.unit"; "OSSVerify.KrLib.Heap.Monad.mupd"; "OSSVerify.KrLib.Heap.Prog.set_brk_ps"; "OSSVerify.KrLib.Heap.Monad.mret"; "OSSVerify.KrLib.Heap.KInv.ev_step_post"; "OSSVerify.KrLib.Heap.Malloc.EBrk"; "OSSVerify.KrLib.Heap.KInv.ld_groups"; "OSSVerify.KrLib.Heap.KInv.ld_metas"; "OSSVerify.KrLib.Lib.Decode.mmap_len"; "OSSVerify.KrLib.Heap.KInv.ld_ceil"; "OSSVerify.KrLib.Heap.KInv.went"; "OSSVerify.KrLib.Heap.KInv.lranges"; "OSSVerify.KrLib.Heap.KInv.ld_resv"; "OSSVerify.KrLib.Heap.Malloc.round_up_pg"; "OSSVerify.KrLib.Heap.KInv.ld_brkreg"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.KInv.lbrk_pages_ok"; "OSSVerify.KrLib.Heap.KInv.brk_quiet"; "OSSVerify.KrLib.Heap.Malloc.PROT_RW"; "OSSVerify.KrLib.Heap.KInv.LEN_MAX"; "OSSVerify.KrLib.Heap.Prog.ev_step"; "OSSVerify.KrLib.Heap.Malloc.EMmap"; "OSSVerify.KrLib.Heap.KInv.MAPF"; "OSSVerify.KrLib.Heap.KInv.BPGuard"; "Stdlib.Lists.List.NoDup"; "Corelib.Lists.ListDef.map"; "OSSVerify.KrLib.Heap.KInv.g_remove"; "OSSVerify.KrLib.Heap.Malloc.EMunmap"; "OSSVerify.KrLib.Heap.KInv.bump_meta"; "Corelib.Init.Logic.False"; "OSSVerify.KrLib.Lib.Nodes.NMprotect"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.PROT_READ"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.PROT_WRITE"; "OSSVerify.KrLib.Lib.Decode.range_ans"; "OSSVerify.KrLib.Lib.Decode.dec_mprotect"; "OSSVerify.KrLib.Lib.Decode.RgDone"; "Corelib.Init.Datatypes.false"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.EMprotect"; "OSSVerify.KrLib.Heap.Malloc.ev"; "OSSVerify.KrLib.Heap.KInv.event_pre"; "OSSVerify.KrLib.Heap.KInv.creach"; "OSSVerify.KrLib.Heap.Prog.ps_m"; "Stdlib.Lists.List.incl"; "OSSVerify.KrLib.Heap.Malloc.cptr"; "OSSVerify.KrLib.Heap.KInv.ld_live"; "OSSVerify.KrLib.Heap.Prog.bptr"; "OWN"; "OSSVerify.KrLib.Heap.Malloc.mstate"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Lemma unsigned_wz : forall z, 0 <= z < 2^64 -> bv_unsigned (wz z) = z.
Proof. intros. unfold wz. apply unsigned_lit. assumption. Qed.

(* [comment removed for export] *)
Lemma ld_ceil_lt63 : forall L pbrk mo, KL L pbrk mo -> ld_ceil L < 2^63.
Proof. intros L pbrk mo HK. exact (ceil_ok_lt63 _ (kl_ceil_ok _ _ _ HK)). Qed.
Lemma alloc_top_KL : forall L pbrk mo, KL L pbrk mo -> alloc_top (m_vmmaps mo) = ld_ceil L.
Proof. intros L pbrk mo HK. symmetry. exact (kl_ceil _ _ _ HK). Qed.

(* [comment removed for export] *)
Lemma region_free_prefix : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Pb,(2.&40.)Psmall,(2.&40.)Pbig,(2.&40.)P,(3.(4.&40.R2.)(4.&40.R1.))P,(5.$6.(7.R5.R4.R2.)$8.)(5.$6.(7.R6.R5.R4.)$8.)")
(* [comment removed for export] *).
Proof.
  induction maps as [|[a sz] maps IH]; intros b small big Hle Hfree; [reflexivity|].
  cbn [region_free] in Hfree |- *.
  apply andb_true_iff in Hfree as [Hhead Htail].
  apply andb_true_iff. split; [|eapply IH; eassumption].
  apply negb_true_iff in Hhead. apply negb_true_iff.
  unfold iv_overlap in Hhead |- *.
  apply andb_false_iff in Hhead. apply andb_false_iff.
  destruct Hhead as [Hhead|Hhead]; [left|right]; apply Z.ltb_ge in Hhead; apply Z.ltb_ge; lia.
Qed.

Lemma elo_went : forall b n, 0 <= b < 2^64 -> elo (went b n) = b.
Proof. intros. unfold elo, went. cbn [fst]. apply unsigned_wz. assumption. Qed.
Lemma ehi_went : forall b n, 0 <= b < 2^64 -> 0 <= n < 2^64 -> ehi (went b n) = b + n.
Proof. intros. unfold ehi, went. cbn [fst snd]. rewrite !unsigned_wz by assumption. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma pwdisj_In : forall l e1 e2, pwdisj l -> In e1 l -> In e2 l -> e1 = e2 \/ edisj e1 e2.
Proof.
  induction l as [|e l IH]; intros e1 e2 Hp H1 H2; [destruct H1|].
  inversion Hp; subst. destruct H1 as [<-|H1], H2 as [<-|H2].
  - left; reflexivity.
  - right. apply H3. exact H2.
  - right. pose proof (H3 _ H1) as D. unfold edisj in *. lia.
  - apply IH; assumption.
Qed.

Lemma region_free_app_r : forall l1 l2 a n, region_free (l1 ++ l2) a n = true -> region_free l2 a n = true.
Proof. induction l1 as [|[e sz] l1 IH]; intros l2 a n H; [exact H|]. cbn in H. apply andb_prop in H as [_ H]. apply IH. exact H. Qed.

Lemma region_free_disj : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Pa,(2.&40.)Pn,(2.&40.)Pe,(1.(2.&40.)(2.&40.))P,(5.$6.(7.R4.R3.R2.)$8.)P,(9.(1.(2.&40.)(2.&40.))R2.R5.)(:.(3.(;.(4.&40.R5.)(4.&40.R4.))(<.R3.))(3.(=.R3.)(4.&40.R5.)))")
(* [comment removed for export] *).
Proof. intros maps a n [e sz] H Hin. unfold elo, ehi. cbn. eapply region_free_In; eauto. Qed.

Lemma vmwf_cons : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Pa,(2.&40.)Pn,(2.&40.)P,(>.R3.)P,(?.(10.(4.&40.R3.)(;.(4.&40.R3.)(4.&40.R2.)))(3.(;.(4.&40.R3.)(4.&40.R2.))(11.+2.+40.)))P,(5.$6.(7.R5.R4.R3.)$8.)(>.(12.(1.(2.&40.)(2.&40.))(13.(2.&40.)(2.&40.)R5.R4.)R6.))")
(* [comment removed for export] *).
Proof.
  intros maps a n [Hb Hp] Hn Hrf. split.
  - intros e [<-|Hin]; [unfold elo, ehi; cbn; lia| apply Hb; exact Hin].
  - constructor; [|exact Hp]. intros e' Hin. pose proof (region_free_disj _ _ _ _ Hrf Hin). unfold edisj, elo, ehi in *. cbn. lia.
Qed.

Lemma pwdisj_filter : forall (f : word * word -> bool) l, pwdisj l -> pwdisj (List.filter f l).
Proof.
  induction l as [|e l IH]; intros Hp; [constructor|]. inversion Hp; subst. cbn. destruct (f e).
  - constructor; [|apply IH; assumption]. intros e' Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply IH; assumption.
Qed.

Lemma vmwf_remove : forall maps a, vmwf maps -> vmwf (map_remove maps a).
Proof.
  intros maps a [Hb Hp]. unfold map_remove. split.
  - intros e Hin. apply List.filter_In in Hin as [Hin _]. auto.
  - apply pwdisj_filter. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_sub : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$14.Phi,$14.Pe,(1.(2.&40.)(2.&40.))P,(10.=(4.&40.R4.))P,(3.(;.(4.&40.R6.)(4.&40.R5.))(11.+2.+40.))P,(9.(1.(2.&40.)(2.&40.))R3.(15.R7.R6.R5.R4.))(?.(3.(4.&40.R8.)(<.R4.))(?.(3.(=.R4.)(;.(4.&40.R8.)(4.&40.R7.)))(10.(<.R4.)(=.R4.))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi e Hsz Hwf Hin. unfold iv_subtract in Hin.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  apply in_app_or in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) (lo)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite unsigned_lit by lia. lia.
  - destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); [|destruct Hin].
    destruct Hin as [<-|[]]. unfold elo, ehi. cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Plo,$14.Phi,$14.Pe,(1.(2.&40.)(2.&40.))P,(9.(1.(2.&40.)(2.&40.))R1.(16.R4.R3.R2.))(17.(1.(2.&40.)(2.&40.))Le0,(1.(2.&40.)(2.&40.))(?.(9.(1.(2.&40.)(2.&40.))R1.R6.)(9.(1.(2.&40.)(2.&40.))R3.(15.(18.(2.&40.)(2.&40.)R1.)(19.(2.&40.)(2.&40.)R1.)R5.R4.))))")
(* [comment removed for export] *).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hin; [destruct Hin|].
  cbn in Hin. apply in_app_or in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity| exact Hin].
  - destruct (IH _ _ _ Hin) as (e0 & H0 & H1). exists e0. split; [right; exact H0| exact H1].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_disjoint : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$14.Phi,$14.P,(?.(10.(4.&40.R4.)(;.(4.&40.R4.)(4.&40.R3.)))(3.(;.(4.&40.R4.)(4.&40.R3.))(11.+2.+40.)))P,(10.R3.R2.)P,(:.(3.(;.(4.&40.R6.)(4.&40.R5.))R4.)(3.R3.(4.&40.R6.)))(5.(0.(1.(2.&40.)(2.&40.)))(15.R7.R6.R5.R4.)(12.(1.(2.&40.)(2.&40.))(13.(2.&40.)(2.&40.)R7.R6.)(1:.(1.(2.&40.)(2.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi Hwf Hlh Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn. rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned. reflexivity.
  - replace (bv_unsigned a <? lo) with false by (symmetry; apply Z.ltb_ge; lia).
    replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    cbn. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma maps_subtract_keep : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Plo,$14.Phi,$14.Pe,(1.(2.&40.)(2.&40.))P,(>.R4.)P,(10.R4.R3.)P,(9.(1.(2.&40.)(2.&40.))R3.R6.)P,(:.(3.(=.R4.)R6.)(3.R5.(<.R4.)))(9.(1.(2.&40.)(2.&40.))R5.(16.R8.R7.R6.))")
(* [comment removed for export] *).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e Hwf Hlh Hin Hd; [destruct Hin|].
  destruct Hwf as [Hb Hp]. cbn. apply in_or_app. destruct Hin as [<-|Hin].
  - left. rewrite iv_subtract_disjoint; [left; reflexivity| | exact Hlh|].
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + unfold elo, ehi in Hd. cbn in Hd. lia.
  - right. apply IH; auto. split; [intros e' H'; apply Hb; right; exact H'| inversion Hp; assumption].
Qed.

(* [comment removed for export] *)
Lemma iv_subtract_contains : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pa,(2.&40.)Psz,(2.&40.)Plo,$14.Phi,$14.Px,$14.Py,$14.P,(10.R4.R3.)P,(10.R4.(11.+2.+40.))P,(3.(4.&40.R8.)R4.)P,(10.R5.R4.)P,(3.R5.(;.(4.&40.R:.)(4.&40.R9.)))P,(:.(3.R6.R9.)(3.R8.R7.))(17.(1.(2.&40.)(2.&40.))Le,(1.(2.&40.)(2.&40.))(?.(9.(1.(2.&40.)(2.&40.))R1.(15.R=.R<.R;.R:.))(?.(3.(<.R1.)R9.)(3.R8.(=.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi x y Hlh Hwf Hax Hxy Hy Hd. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct Hd as [Hd|Hd].
  - replace (bv_unsigned a <? lo) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; left; left; reflexivity|]. unfold elo, ehi; cbn. rewrite unsigned_lit by lia. lia.
  - replace (hi <? bv_unsigned a + bv_unsigned sz) with true by (symmetry; apply Z.ltb_lt; lia).
    eexists. split; [apply in_or_app; right; left; reflexivity|]. unfold elo, ehi; cbn. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma maps_subtract_In_intro : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Plo,$14.Phi,$14.Pe,(1.(2.&40.)(2.&40.))Pe',(1.(2.&40.)(2.&40.))P,(9.(1.(2.&40.)(2.&40.))R2.R5.)P,(9.(1.(2.&40.)(2.&40.))R2.(15.(18.(2.&40.)(2.&40.)R3.)(19.(2.&40.)(2.&40.)R3.)R5.R4.))(9.(1.(2.&40.)(2.&40.))R3.(16.R7.R6.R5.))")
(* [comment removed for export] *).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi e e' Hin H'; [destruct Hin|].
  cbn. apply in_or_app. destruct Hin as [<-|Hin]; [left; exact H'| right; eapply IH; eauto].
Qed.

Lemma pwdisj_app : forall P R, pwdisj P -> pwdisj R -> (forall p r, In p P -> In r R -> edisj p r) -> pwdisj (P ++ R).
Proof.
  induction P as [|p P IH]; intros R HP HR Hx; [exact HR|]. inversion HP; subst. cbn. constructor.
  - intros e' He'. apply in_app_or in He' as [He'|He']; [auto|]. apply Hx; [left; reflexivity| exact He'].
  - apply IH; auto. intros p' r Hp' Hr. apply Hx; [right; exact Hp'| exact Hr].
Qed.

Lemma iv_subtract_pwdisj : forall a sz lo hi, lo < hi -> hi < 2^64 -> pwdisj (iv_subtract a sz lo hi).
Proof.
  intros a sz lo hi Hlh Hwf. unfold iv_subtract.
  pose proof (bv_unsigned_in_range 64 a). pose proof (bv_unsigned_in_range 64 sz). unfold bv_modulus in *.
  destruct (Z.ltb_spec (bv_unsigned a) (lo)); destruct (Z.ltb_spec (hi) (bv_unsigned a + bv_unsigned sz)); cbn [app].
  - constructor; [|constructor; [intros e' []| constructor]]. intros e' [<-|[]].
    unfold edisj, elo, ehi; cbn. rewrite !unsigned_lit by lia. left. lia.
  - constructor; [intros e' []| constructor].
  - constructor; [intros e' []| constructor].
  - constructor.
Qed.

Lemma vmwf_subtract : forall maps lo hi, lo < hi -> hi < 2^64 -> vmwf maps -> vmwf (maps_subtract maps lo hi).
Proof.
  induction maps as [|[a sz] maps IH]; intros lo hi Hlh Hhi [Hb Hp]; [split; [intros e []| constructor]|].
  inversion Hp; subst. assert (Hwf' : vmwf maps) by (split; [intros e He; apply Hb; right; exact He| assumption]).
  specialize (IH lo hi Hlh Hhi Hwf'). destruct IH as [IHb IHp].
  assert (Ha : elo (a, sz) < ehi (a, sz) <= 2^64) by (apply Hb; left; reflexivity). unfold elo, ehi in Ha; cbn in Ha.
  cbn. split.
  - intros e Hin. apply in_app_or in Hin as [Hin|Hin]; [|apply IHb; exact Hin].
    pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) Hin). lia.
  - apply pwdisj_app; [apply iv_subtract_pwdisj; [exact Hlh| exact Hhi]| exact IHp|].
    intros e e' He He'. pose proof (iv_subtract_sub a sz lo hi e ltac:(lia) ltac:(lia) He) as S1.
    destruct (maps_subtract_In _ _ _ _ He') as (e0 & H0 & H0').
    assert (W0 : elo e0 < ehi e0 <= 2^64) by (apply Hb; right; exact H0). destruct e0 as [a0 s0]. unfold elo, ehi in W0; cbn in W0.
    pose proof (iv_subtract_sub a0 s0 lo hi e' ltac:(lia) ltac:(lia) H0') as S2.
    pose proof (H1 _ H0) as D. unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma wcov_mono : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Pmaps',(0.(1.(2.&40.)(2.&40.)))Plo,$14.Phi,$14.P,Pe,(1.(2.&40.)(2.&40.))P,(9.(1.(2.&40.)(2.&40.))R1.R5.)(9.(1.(2.&40.)(2.&40.))R2.R5.)P,(1;.R5.R3.R2.)(1;.R5.R4.R3.)")
(* [comment removed for export] *).
Proof. intros maps maps' lo hi Hs Hc x Hx. ddestruct (Hc x Hx) as (e & He & Hr). exists e. auto. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_vmmaps_forget_vm_ranges : forall rs m, m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.

Lemma nstep_brk_inv : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Preq,$14.Pmo,$1<.Prsp,$1=.Pmo',$1<.Pevs,(0.$1>.)P,(1?.(20.R5.)R4.R3.R2.R1.)Zh,$21.(22.R5.)(17.(2.&40.)Lr,(2.&40.)(?.(5.$6.(23.R7.(24.&40.R8.)R1.)$8.)(?.(5.$21.(22.R5.)(25.R2.(24.&40.R8.)R1.))(?.(5.$1=.R6.(26.R1.(1:.(1.(2.&40.)(0.(2.&8.))))(27.(24.&40.R8.)R1.(28.R2.))(29.R1.(28.R2.))(1:.$2:.)(1:.(1.(2.&40.)$2;.))))(5.(0.$1>.)R4.(1:.$1>.))))))")
(* [comment removed for export] *).
Proof.
  intros req mo rsp mo' evs H. destruct (Decode.nstep_brk_inv _ _ _ _ _ H) as (r & Hr & -> & -> & ->).
  exists r. split; [exact Hr|]. split; [|split; reflexivity].
  unfold with_brk_next. rewrite m_vmmaps_forget_vm_ranges. reflexivity.
Qed.

Lemma brk_unmaps_nogrow' : forall r old, bv_unsigned old <= bv_unsigned r -> brk_unmaps r old = [].
Proof. intros. apply brk_unmaps_nogrow. assumption. Qed.

(* [comment removed for export] *)
Lemma brk_model_next_query : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Ph,$21.Zh',$21.(25.R1.(24.&40.=)(28.R1.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2<.R1.)(2<.R2.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2=.R1.)(2=.R2.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2>.R1.)(2>.R2.))(?.(5.(2.&40.)(2?.R1.)(2?.R2.))(5.(2.&40.)(28.R1.)(28.R2.))))))")
(* [comment removed for export] *).
Proof.
  intros h. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. change (w_is0 (Z_to_bv 64 0)) with true. cbn [negb andb app].
  rewrite brk_unmaps_nogrow' by lia. cbn. repeat split; reflexivity.
Qed.

Lemma brk_r_ok_query : forall mo r, brk_r_ok mo (Z_to_bv 64 0) r = true -> r = vm_brk (m_vmmaps mo).
Proof. intros mo r H. unfold brk_r_ok in H. change (w_is0 (Z_to_bv 64 0)) with true in H. cbn [orb] in H. apply bv_eqb_eq in H. exact H. Qed.

(* [comment removed for export] *)
Lemma brk_model_next_same : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Ph,$21.Preq,(2.&40.)Zh',$21.(25.R2.R1.(28.R2.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2<.R1.)(2<.R3.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2=.R1.)(2=.R3.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2>.R1.)(2>.R3.))(?.(5.(2.&40.)(2?.R1.)(2?.R3.))(5.(2.&40.)(28.R1.)(28.R3.))))))")
(* [comment removed for export] *).
Proof.
  intros h req. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite Z.ltb_irrefl, andb_false_r. unfold brk_grants, brk_is_grow. rewrite Z.ltb_irrefl, andb_false_r. cbn [app].
  rewrite brk_unmaps_nogrow' by lia. cbn. repeat split; reflexivity.
Qed.

(* [comment removed for export] *)
Lemma brk_model_next_grown : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Ph,$21.Preq,$14.Zb,$14.(4.&40.(28.R2.))P,(10.=R1.)P,(?.(10.R2.R3.)(10.R3.(11.+2.+40.)))Zh',$21.(25.R5.(24.&40.R4.)(24.&40.R4.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2<.R1.)(2<.R6.))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2=.R1.)(12.(1.(2.&40.)(2.&40.))(13.(2.&40.)(2.&40.)(28.R6.)(24.&40.(30.R5.R4.)))(2=.R6.)))(?.(5.(0.(1.(2.&40.)(2.&40.)))(2>.R1.)(2>.R6.))(?.(5.(2.&40.)(2?.R1.)(2?.R6.))(5.(2.&40.)(28.R1.)(24.&40.R5.))))))")
(* [comment removed for export] *).
Proof.
  intros h req b Hb Hreq h'. subst h'. cbn [brk_model_next vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk].
  unfold brk_maps_next. rewrite unsigned_lit by lia. fold b.
  replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (req <? b) with false by (symmetry; apply Z.ltb_ge; lia). cbn [andb].
  unfold brk_grants, brk_is_grow. rewrite w_is0_lit by lia. replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
  rewrite unsigned_lit by lia. fold b. replace (0 <? b) with true by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true by (symmetry; apply Z.ltb_lt; lia). cbn [negb andb app].
  rewrite brk_unmaps_nogrow' by (rewrite unsigned_lit by lia; lia).
  assert (Hsub : (Z_to_bv 64 req - vm_brk h)%bv = Z_to_bv 64 (req - b)).
  { apply bv_eq. rewrite bv_sub_unsigned, unsigned_lit by lia. fold b. rewrite Z_to_bv_unsigned. reflexivity. }
  rewrite Hsub. cbn. repeat split; reflexivity.
Qed.

Lemma brk_r_ok_grow : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmo,$1<.Preq,$14.Pr,(2.&40.)Zh,$21.(22.R3.)Zb,$14.(4.&40.(28.R1.))P,(3.(4.&40.(2?.R2.))R1.)P,(?.(10.R2.R5.)(10.R5.(11.+2.+40.)))P,(5.$6.(23.R7.(24.&40.R6.)R5.)$8.)(:.(5.(2.&40.)R6.(28.R5.))(?.(5.(2.&40.)R6.(24.&40.R7.))(5.$6.(31.R8.(24.&40.R7.)(24.&40.R7.))$8.)))")
(* [comment removed for export] *).
Proof.
  intros mo req r h b Hs Hreq H. pose proof (bv_unsigned_in_range 64 (vm_brk h)) as Hr0. unfold bv_modulus in Hr0. fold b in Hr0.
  unfold brk_r_ok in H. rewrite w_is0_lit in H by lia.
  replace (req =? 0) with false in H by (symmetry; apply Z.eqb_neq; lia).
  unfold min_brk in H. fold h in H. rewrite unsigned_lit in H by lia.
  replace (req <? bv_unsigned (vm_start_brk h)) with false in H by (symmetry; apply Z.ltb_ge; lia).
  fold b in H. replace (req <? b) with false in H by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in H.
  apply andb_prop in H as [H1 H2]. apply orb_prop in H1 as [H1|H1]; apply bv_eqb_eq in H1; subst r; [right|left]; auto.
Qed.

Lemma brk_grow_ok_facts : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmo,$1<.Preq,$14.Zh,$21.(22.R2.)Zb,$14.(4.&40.(28.R1.))P,(10.=R1.)P,(?.(10.R2.R4.)(10.R4.(11.+2.+40.)))P,(5.$14.(32.R3.+1000.)=)P,(5.$14.(32.R6.+1000.)=)P,(5.$6.(31.R8.(24.&40.R7.)(24.&40.R7.))$8.)(?.(3.R8.(33.R7.))(?.(5.$6.(7.(34.(1.(2.&40.)(2.&40.))(2<.R7.)(2=.R7.))(24.&40.R6.)(24.&40.(30.R8.R6.)))$8.)(5.$6.(7.(34.(1.(2.&40.)(2.&40.))(2<.R7.)(2=.R7.))(24.&40.R6.)(24.&40.(30.(;.R8.+1000.)R6.)))$8.)))")
(* [comment removed for export] *).
    (* [comment removed for export] *)
Proof.
  intros mo req h b Hb Hreq Hba Hra H. pose proof (alloc_top_lt h) as Htop. unfold two_pow_64 in Htop.
  unfold brk_grow_ok in H. fold h in H. rewrite unsigned_lit in H by lia. fold b in H.
  replace (0 <? b) with true in H by (symmetry; apply Z.ltb_lt; lia).
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [andb] in H.
  unfold page_round_up_Z in H. rewrite page_size_eq in H.
  replace ((b + 4096 - 1) / 4096 * 4096) with b in H.
  2:{ pose proof (Z_div_mod_eq_full b 4096). pose proof (Z_div_mod_eq_full (b+4096-1) 4096). pose proof (Z.mod_pos_bound (b+4096-1) 4096). nia. }
  replace ((req + 4096 - 1) / 4096 * 4096) with req in H.
  2:{ pose proof (Z_div_mod_eq_full req 4096). pose proof (Z_div_mod_eq_full (req+4096-1) 4096). pose proof (Z.mod_pos_bound (req+4096-1) 4096). nia. }
  replace (b <? req) with true in H by (symmetry; apply Z.ltb_lt; lia).
  apply andb_prop in H as [H _]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1.
  split; [exact H1|]. split; [|exact H2].
  eapply region_free_prefix; [|exact H2]. rewrite !unsigned_lit by lia. lia.
Qed.

Lemma nsafe_mmap_fixed : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pa,$14.Pmo,$1<.Zh,$21.(22.R1.)Zaw,(2.&40.)(24.&40.R3.)Zn,(2.&40.)(24.&40.$35.)P,(10.=R5.)P,(3.(;.R6.$35.)(33.R4.))P,(5.$14.(32.R7.+1000.)=)P,(5.$6.(7.(2<.R6.)R5.R4.)$8.)P,(5.$6.(36.(2=.R7.)R6.R5.)$8.)(37.(38.R:.$35.$39.$3:.)R9.)")
(* [comment removed for export] *).
Proof.
  intros a mo h aw n Ha Hc Hal Hrf Hmc. pose proof (alloc_top_lt h) as Hcl. unfold two_pow_64 in Hcl.
  cbn [nsafe]. split; [reflexivity|]. unfold mmap_safe_b.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true.   (* [comment removed for export] *)
  change (mmap_anon_b (Z_to_bv 64 MAPFX)) with true.
  rewrite w_is0_lit by (unfold PGSZ; lia). change (PGSZ =? 0) with false.
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false.
  change (mmap_fixed_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with true.
  cbn [negb andb orb]. cbv zeta. rewrite (unsigned_lit PGSZ) by (unfold PGSZ; lia). change (page_round_up_Z PGSZ) with PGSZ.
  fold aw. replace (bv_unsigned aw) with a by (subst aw; symmetry; apply unsigned_lit; unfold PGSZ in *; lia).
  replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
  fold h. replace (a + PGSZ <=? alloc_top h) with true by (symmetry; apply Z.leb_le; lia). cbn [negb].
  rewrite page_size_eq, Hal. cbn [Z.eqb negb]. replace (0 <? a) with true by (symmetry; apply Z.ltb_lt; lia).
  cbn [negb]. fold n. rewrite Hrf, Hmc. reflexivity.
Qed.

Lemma nstep_mmap_fixed_inv : forall a mo rsp mo' evs,
  let h := m_vmmaps mo in
  let aw := Z_to_bv 64 a in let n := Z_to_bv 64 PGSZ in
  minv mo ->
  0 < a -> a + PGSZ <= alloc_top h -> a mod 4096 = 0 ->
  region_free (vm_reserved h) aw n = true -> map_contains (vm_maps h) aw n = true ->
  nstep (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists x, dec_mmap_fixed a PGSZ rsp = Some x /\
  match x with
  | FxKept e => e = ENOMEM /\ mo' = mo
  | FxDone => m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) ((aw, n) :: maps_subtract (vm_noaccess h) a (a + PGSZ))
                                         (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  | FxLost e => e = ENOMEM /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (maps_subtract (vm_maps h) a (a + PGSZ))
                                           (maps_subtract (vm_noaccess h) a (a + PGSZ))
                                           (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h)
  end.
Proof.
  intros a mo rsp mo' evs h aw n Hm Ha Hc Hal Hrf Hmc H.
  pose proof (alloc_top_lt h) as Hcl. unfold two_pow_64 in Hcl.
  pose proof (nsafe_mmap_fixed a mo Ha Hc Hal Hrf Hmc) as Hsafe.
  pose proof (nstep_mm_vm_only (NMmap a PGSZ PROT_NONE MAPFX) mo rsp mo' evs Hm Hsafe H) as [Hv ->]. split; [reflexivity|]. split; [exact Hv|].
  apply nstep_mmap_iff in H as [_ H]. destruct rsp as [r ws zs us cs ci]. unfold check_mmap in H. kill_extra cs ci H.
  change (mmap_off_aligned_b (Z_to_bv 64 0)) with true in H.   (* [comment removed for export] *)
  change (mmap_anon_b (Z_to_bv 64 MAPFX)) with true in H. cbn [negb] in H. cbv iota in H.
  rewrite w_is0_lit in H by (unfold PGSZ; lia). change (PGSZ =? 0) with false in H.
  change (mmap_modeled_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false in H.
  change (mmap_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with false in H.
  change (mmap_fixed_noaccess_b (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 0)) with true in H.
  cbv iota beta in H. fold aw h in H. rewrite (unsigned_lit PGSZ) in H by (unfold PGSZ; lia).
  change (page_round_up_Z PGSZ) with PGSZ in H. fold n in H.
  assert (Haw : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia). rewrite Haw in H.
  replace (two_pow_64 <=? a + PGSZ) with false in H by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia).
  replace (a + PGSZ <=? alloc_top h) with true in H by (symmetry; apply Z.leb_le; lia). cbn [negb] in H.
  rewrite page_size_eq, Hal in H. cbn [Z.eqb negb] in H.
  replace (0 <? a) with true in H by (symmetry; apply Z.ltb_lt; lia). cbn [negb] in H.
  cbv zeta in H. fold n in H. rewrite Hrf, Hmc in H. cbn [andb] in H.
  assert (Hn : bv_unsigned n = PGSZ) by (subst n; apply unsigned_lit; unfold PGSZ; lia).
  change (mmap_len PGSZ) with PGSZ. fold n.
  destruct ws; [|discriminate]. destruct zs; [|discriminate].
  destruct (errno_ret_in mmap_errnos r) eqn:Herr.
  - apply errno_ret_in_true in Herr as (e & HIn & ->). cbn in HIn. destruct HIn as [<-|[]].
    destruct us as [|u us'].
    + injection H as <-. exists (FxKept ENOMEM). split; [|split; reflexivity].
      unfold dec_mmap_fixed. rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity.
    + (* [comment removed for export] *)
      destruct (listNN_eqb (u :: us') [(aw, n)]) eqn:E; [|discriminate].
      first [ discriminate H
            | injection H as <-;
              apply listNN_eqb_eq in E; injection E as -> ->;
              exists (FxLost ENOMEM); split; [|split; [reflexivity|]];
              [ unfold dec_mmap_fixed; subst aw n; rewrite !bv_eqb_refl; cbn [andb];
                rewrite errno_of_errno_ret by (unfold ENOMEM; lia); reflexivity
              | unfold with_mmap_destroyed; rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps;
                unfold mmap_fixed_destroyed_next; fold h; rewrite Haw, Hn; reflexivity ] ].
  - destruct (bv_eqb r aw && listNN_eqb us [(aw, n)]) eqn:E; [|discriminate]. injection H as <-.
    apply andb_prop in E as [E1 E2]. apply bv_eqb_eq in E1. apply listNN_eqb_eq in E2. subst r us.
    exists FxDone. split.
    + unfold dec_mmap_fixed. subst aw n. rewrite !bv_eqb_refl. cbn [andb].
      change (mmap_len PGSZ) with PGSZ. rewrite ?bv_eqb_refl. cbn [andb].
      rewrite errno_of_lit by (unfold PGSZ in *; lia). reflexivity.
    + unfold with_mmap_replacement. rewrite with_mmap_backing_plain by reflexivity.
      rewrite m_vmmaps_vm_forget_range, m_vmmaps_with_vmmaps. rewrite Hn. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma nstep_dec_brk : forall req mo rsp mo' evs,
  let h := m_vmmaps mo in
  minv mo ->
  (0 < bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_start_brk h) <= bv_unsigned (vm_brk h))%Z ->
  (bv_unsigned (vm_brk h) <= req < 2^64)%Z ->
  nstep (NBrk req) mo rsp mo' evs ->
  evs = [] /\ vm_only mo mo' /\
  exists a, dec_brk (bv_unsigned (vm_brk h)) req rsp = Some a /\
  match a with
  | BrkSame => vm_brk (m_vmmaps mo') = vm_brk h
  | BrkGrown => vm_brk (m_vmmaps mo') = Z_to_bv 64 req
  end.
Proof.
  intros req mo rsp mo' evs h Hm Hb Hsb Hreq H.
  ddestruct (Decode.nstep_dec_brk req mo rsp mo' evs Hm Hb Hsb Hreq H) as (E & Hv & a & Hd & Ha).
  split; [exact E|]. split; [exact Hv|]. exists a. split; [exact Hd|].
  destruct a; [ddestruct Ha as (_ & _ & ->)| rewrite Ha]; reflexivity.
Qed.

Ltac nsafe_assert :=
  lazymatch goal with |- nsafe ?n ?mo /\ _ => assert (Hsafe : nsafe n mo); [| split; [exact Hsafe|]] end.

Ltac kl_open HK := destruct HK as [Kminv Khalt Kwf Kceil Kcok Kresv Krt Kstart Kgr Kme Kdis Kreg Kph].

(* [comment removed for export] *)
Lemma KL_vm_eq : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.Ppbrk,$14.Pmo,$1<.Pmo',$1<.P,(3<.R4.R3.R2.)P,(3=.R2.)P,(5.(3>.(2.&40.))(3?.R3.)(40.(2.&40.)))P,(5.(0.(1.(2.&40.)(2.&40.)))(2<.(22.R4.))(2<.(22.R5.)))P,(5.(0.(1.(2.&40.)(2.&40.)))(2=.(22.R5.))(2=.(22.R6.)))P,(5.(0.(1.(2.&40.)(2.&40.)))(2>.(22.R6.))(2>.(22.R7.)))P,(5.(2.&40.)(2?.(22.R7.))(2?.(22.R8.)))P,(5.(2.&40.)(28.(22.R8.))(28.(22.R9.)))P,(5.$14.(33.(22.R9.))(33.(22.R:.)))(3<.R=.R<.R:.)")
(* [comment removed for export] *).
Proof.
  intros L pbrk mo mo' K Hmi Hh H1 H2 H3 H4 H5 H6. kl_open K; constructor; rewrite ?H1, ?H2, ?H3, ?H4, ?H5, ?H6; auto.
Qed.

(* [comment removed for export] *)
Definition phase_inv (ph : brk_phase) (L : mled) (pbrk : Z) (mo : Model) : Prop :=
  match ph with
  | BPUntried => vm_brk (m_vmmaps mo) = vm_start_brk (m_vmmaps mo) /\ ld_brkreg L = None
  | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur /\ pbrk = cur /\ ld_brkreg L = None
  | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo))
      /\ bv_unsigned (vm_brk (m_vmmaps mo)) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
      /\ ld_brkreg L = None /\ cur + 2 * PGSZ <= ld_ceil L
      /\ (exists e, In e (vm_maps (m_vmmaps mo)) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
      /\ (forall b l, In (b, l) (ld_groups L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
      /\ (forall b l k, In (b, l, k) (ld_metas L) -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
  | BPLive => exists b l, ld_brkreg L = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo)) = b + l /\ pbrk = b + l
  | BPDead => True
  end.

Lemma KL_rephase : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.Pph,$41.Ppbrk,$14.Ppbrk',$14.Pmo,$1<.P,(3<.R5.R3.R1.)P,(42.R5.R6.R3.R2.)(3<.(43.R6.R7.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros L ph pbrk pbrk' mo K Hph. kl_open K; constructor; cbn; auto. Qed.

Lemma KL_dead : forall L pbrk pbrk' mo, KL L pbrk mo -> KL (set_brkph BPDead L) pbrk' mo.
Proof. intros. eapply KL_rephase; [eassumption| exact I]. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk0_ok : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.PG,P,$44.P,$1<.SpPs0,$44.P,(45.R2.)P,(5.$41.(46.R4.)$47.)(48.$44.$14.Ls,$44.Lmo,$1<.(?.(5.$44.R2.R5.)(?.(3<.R7.(49.R2.)R1.)A2.R6.R2.R1.))(4:.$44.$14.$14.(4;.$44.$14.(20.=)$4<.)Lr,$14.(4:.$44.$4=.$14.(4>.$44.(4?.R1.))L,$4=.(50.$44.$14.R2.)))(51.R5.(52.=)R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros L G s0 HG Hph.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk 0) dec_brk0 _ (fun r s mo => s = s0 /\ G s mo /\ brk0_answer_ok r = true /\ KL (set_brkph (BPQueried r) L) r mo)).
    (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). nsafe_assert; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_brk0 _ _ _ _ (kl_minv _ _ _ HK) Hst) as (_ & Hdec & Hvo & Emo').
    assert (Hbrk : vm_brk (m_vmmaps mo') = vm_brk (m_vmmaps mo)) by (rewrite Emo'; reflexivity).
    exists (bv_unsigned (vm_brk (m_vmmaps mo))). split; [exact Hdec|].
    assert (HK' : KL L (ps_brk s0) mo').
    { eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | |]; rewrite Emo'; reflexivity. }
    pose proof (kl_phase _ _ _ HK') as Kph. rewrite Hph in Kph. destruct Kph as [Ebrk Ereg].
    pose proof (kl_start _ _ _ HK') as (S1 & S2 & S3 & S4).
    splits.
    - reflexivity.
    - eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs].
    - unfold brk0_answer_ok. rewrite <- Hbrk, Ebrk. pose proof (bv_unsigned_in_range 64 (vm_start_brk (m_vmmaps mo'))) as R. unfold bv_modulus in R.
      unfold TWO64. rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite S2, Z.eqb_refl. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
    - eapply KL_rephase; [exact HK'|]. cbn [phase_inv]. rewrite <- Hbrk, Ebrk. splits; auto. }
  intros r. cbn beta. eapply mspec_bind.
  { apply mspec_upd. }
  intros []. apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (s1 & -> & -> & HGs & Hans & HK)). unfold ev_step_post. cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post Z.eqb].
  splits; auto. eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
Qed.

Lemma mspec_get_bind_eq {St A} (s0 : St) (P : assn St) (f : St -> Monad.M St A) Q :
  mspec (fun s mo => s = s0 /\ P s mo) (f s0) Q -> mspec (fun s mo => s = s0 /\ P s mo) (x <- mget ;; f x) Q.
Proof. intros H s mo [-> HP]. unfold mbind, mget. cbn. apply H. auto. Qed.

Lemma elo_pair : forall a n, elo (a, n) = bv_unsigned a. Proof. reflexivity. Qed.
Lemma ehi_pair : forall a n, ehi (a, n) = bv_unsigned a + bv_unsigned n. Proof. reflexivity. Qed.

Lemma went_In_bounds : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.Ppbrk,$14.Pmo,$1<.Pb,$14.Pl,$14.P,(3<.R5.R4.R3.)P,(:.(9.(1.$14.$14.)(13.$14.$14.R3.R2.)(53.R6.))(17.$14.Lk,$14.(9.(1.(1.$14.$14.)$14.)(13.(1.$14.$14.)$14.(13.$14.$14.R4.R3.)R1.)(54.R7.))))(?.(10.=R4.)(?.(10.=(55.R3.))(?.(3.(;.R4.(55.R3.))(56.R7.))(?.(9.(1.(2.&40.)(2.&40.))(57.R4.(55.R3.))(2=.(22.R5.)))(?.(5.$14.(<.(57.R4.(55.R3.)))R4.)(5.$14.(=.(57.R4.(55.R3.)))(;.R4.(55.R3.))))))))")
(* [comment removed for export] *).
Proof.
  intros L pbrk mo b l K Hin. pose proof (ld_ceil_lt63 _ _ _ K).
  assert (0 < l < LEN_MAX /\ 0 < b /\ b + mmap_len l <= ld_ceil L /\ In (went b (mmap_len l)) (vm_maps (m_vmmaps mo))) as (Hl & Hb & Hc & Hm).
  { destruct Hin as [Hin|[k Hin]]; [pose proof (kl_groups _ _ _ K _ _ Hin)| pose proof (kl_metas _ _ _ K _ _ _ Hin)]; tauto. }
  pose proof (mmap_len_ge l ltac:(lia)). splits; auto; try lia.
  - apply elo_went. lia.
  - apply ehi_went; lia.
Qed.

Lemma In_lranges : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.Px,(1.$14.$14.)P,(9.(1.$14.$14.)R1.(58.R2.))(:.(9.(1.$14.$14.)R2.(59.R3.))(:.(17.$14.Lb,$14.(17.$14.Ll,$14.(?.(9.(1.$14.$14.)(13.$14.$14.R2.R1.)(53.R5.))(5.(1.$14.$14.)R4.(13.$14.$14.R2.(5:.R1.))))))(:.(17.$14.Lb,$14.(17.$14.Ll,$14.(17.$14.Lk,$14.(?.(9.(1.(1.$14.$14.)$14.)(13.(1.$14.$14.)$14.(13.$14.$14.R3.R2.)R1.)(54.R6.))(5.(1.$14.$14.)R5.(13.$14.$14.R3.(5:.R2.)))))))(17.$14.Lb,$14.(17.$14.Ll,$14.(?.(5.(3>.(1.$14.$14.))(5;.R5.)(5<.(1.$14.$14.)(13.$14.$14.R2.R1.)))(5.(1.$14.$14.)R4.(13.$14.$14.(;.R2.$35.)(30.(5:.R1.)$35.)))))))))")
(* [comment removed for export] *).
Proof.
  intros L x Hin. unfold lranges in Hin. rewrite !in_app_iff in Hin. destruct Hin as [H|[H|[H|H]]].
  - left; exact H.
  - right; left. apply in_map_iff in H as ([b l] & <- & H). dexists b, l. auto.
  - right; right; left. apply in_map_iff in H as ([[b l] k] & <- & H). dexists b, l, k. auto.
  - right; right; right. destruct (ld_brkreg L) as [[b l]|]; [|destruct H]. destruct H as [<-|[]]. dexists b, l. auto.
Qed.

(* [comment removed for export] *)
Lemma KL_lbrk_pages_ok : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.Ppbrk,$14.Pmo,$1<.Plo,$14.Plen,$14.P,(3<.R5.R4.R3.)Zh,$21.(22.R4.)P,(10.=R4.)P,(10.=R4.)P,(3.(;.R6.R5.)(56.R9.))P,(5.$6.(7.(34.(1.(2.&40.)(2.&40.))(2<.R4.)(2=.R4.))(24.&40.R7.)(24.&40.R6.))$8.)P,Pb,$14.Pl,$14.P,(5.(3>.(1.$14.$14.))(5;.R=.)(5<.(1.$14.$14.)(13.$14.$14.R2.R1.)))(?.(5.$14.(32.R2.$35.)=)(:.(3.(;.R3.R2.)R;.)(3.(;.R;.R:.)(;.R3.$35.))))(5.$6.(5=.R<.R9.R8.)$8.)")
(* [comment removed for export] *).
Proof.
  intros L pbrk mo lo len HK h Hlo Hlen Hceil Hrf Hbrk. pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl.
  assert (Ulo : bv_unsigned (Z_to_bv 64 lo) = lo) by (apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  unfold lbrk_pages_ok. rewrite (proj2 (Z.ltb_lt 0 lo)) by lia. rewrite (proj2 (Z.leb_le _ _) Hceil). cbn [andb].
  unfold ranges_free. apply forallb_forall. intros [b0 m0] Hin. cbn [fst snd]. unfold iv_disjoint.
  enough (lo + len <= b0 \/ b0 + m0 <= lo) as D.
  { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
  apply In_lranges in Hin as [H|[(b1 & l1 & H & E)|[(b1 & l1 & k & H & E)|(b1 & l1 & H & E)]]].
  - rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
    pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ulo, Ulen in D. exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_introl H)) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. pose proof (went_In_bounds _ _ _ b1 l1 HK (or_intror (ex_intro _ k H))) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ulo, Ulen in D. rewrite round_up_pg_eq. fold (mmap_len l1). exact D.
  - injection E as -> ->. destruct (Hbrk b1 l1 H) as [Al D]. rewrite round_up_pg_aligned by (unfold PGSZ in Al; exact Al). lia.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk_grow1_ok : forall L G s0 cur, frame_ok G -> ld_brk L = BPQueried cur ->
  let req := round_up_pg cur + 2 * PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0).
Proof.
  intros L G s0 cur HG Hph req.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> cur /\ 0 < req) /\ ps_brk s0 = cur /\
                match a with
                | BrkGrown => KL (set_brkph (BPGuard cur) L) req mo /\ lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true
                | BrkSame => KL (set_brkph BPDead L) cur mo
                end)).
    (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). nsafe_assert; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl. pose proof (kl_ceil _ _ _ HK) as Kcl.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. ddestruct Kph as (Ecur & Ebrk & Epbrk & Ereg).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Hreq : req = cur + 2 * PGSZ). { subst req. rewrite round_up_pg_aligned; [reflexivity|]. rewrite Ecur. exact S2. }
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    pose proof (nstep_dec_brk req mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    apply brk_r_ok_grow in Hr; [| fold h; lia| fold h; unfold PGSZ in *; lia]. fold h in Hr.
    dpose (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    dpose (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply brk_grow_ok_facts in Hgo; fold h in Hgo; [| fold h; lia| fold h; unfold PGSZ in *; lia| fold h; rewrite Ebrk, Ecur; exact S2| rewrite Hreq, Ecur; unfold PGSZ in *; rewrite Z.add_mod, S2 by lia; reflexivity].
      ddestruct Hgo as (Hceil & Hrf & _). rewrite <- Kcl in Hceil.
      assert (HPG : lbrk_pages_ok L (round_up_pg cur) (2 * PGSZ) = true).
      { rewrite round_up_pg_aligned by (rewrite Ecur; unfold PGSZ in S2; exact S2).
        apply (KL_lbrk_pages_ok L (ps_brk s0) mo cur (2 * PGSZ) HK); [lia| unfold PGSZ; lia| lia| | intros b l Hb; rewrite Ereg in Hb; discriminate].
        replace cur with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 (2 * PGSZ)) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = 2 * PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      split; [|exact HPG].
      kl_open HK. constructor; rewrite ?Emo'; cbn [m_vmmaps with_vmmaps set_brkph ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b l Hin. specialize (Kgr b l Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l k Hin. specialize (Kme b l k Hin). unfold brk_disj in *. cbn. intuition auto with datatypes.
      + intros b l Hb. rewrite Ereg in Hb. discriminate.
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; try lia.
        * exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
        * intros b l Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kceil Kcok Kresv Krt Kstart Kgr Kme Kdis Kreg Kph) (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
        * intros b l k Hin. pose proof (went_In_bounds _ _ _ b l (mkKL _ _ _ Kminv Khalt Kwf Kceil Kcok Kresv Krt Kstart Kgr Kme Kdis Kreg Kph) (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
          pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D. lia.
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | |]; rewrite Emo'; cbn [m_vmmaps with_vmmaps]; first [assumption | reflexivity]. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    (intros s mo dd_H; ddestruct dd_H as (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & [HK HPG])). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Z.eqb_refl.
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (-> & HGs & [Hne Hpos] & Ecur & HK)). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ecur.
    replace (cur =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_brk_grow2_ok : forall L G s0 b l, frame_ok G -> ld_brk L = BPLive -> ld_brkreg L = Some (b, l) ->
  let req := b + l + PGSZ in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (s <- mget ;; a <- msys (NBrk req) (dec_brk (ps_brk s) req) ;;
         match a with BrkGrown => mupd (set_brk_ps req) ;;; mret req | BrkSame => mret (ps_brk s) end)
        (ev_step_post L (EBrk req) G s0).
Proof.
  intros L G s0 b l HG Hph Ereg req.
  apply mspec_get_bind_eq.
  eapply mspec_bind.
  { apply (mspec_sys (NBrk req) (dec_brk (ps_brk s0) req) _
             (fun a s mo => s = s0 /\ G s mo /\ (req <> b + l /\ 0 < req) /\ ps_brk s0 = b + l /\
                match a with
                | BrkGrown => KL (set_brkreg (Some (b, l + PGSZ)) L) req mo /\ lbrk_pages_ok L (b + l) PGSZ = true
                | BrkSame => KL (set_brkph BPDead L) (b + l) mo
                end)).
    (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). nsafe_assert; [exact I|].
    intros rsp mo' evs Hst.
    pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl. pose proof (kl_ceil _ _ _ HK) as Kcl.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. ddestruct Kph as (b' & l' & Ereg' & Ebrk & Epbrk).
    rewrite Ereg in Ereg'. injection Ereg' as <- <-.
    pose proof (kl_brkreg _ _ _ HK b l Ereg) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    pose proof (nstep_brk_inv _ _ _ _ _ Hst) as (r & Hr & Emo' & _ & _).
    pose proof (nstep_dec_brk req mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(unfold PGSZ in *; lia) Hst) as (_ & Hvo & a & Hdec & Ha).
    set (h := m_vmmaps mo) in *.
    rewrite Ebrk in Hdec. rewrite Epbrk. exists a. split; [exact Hdec|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    split; [unfold PGSZ in *; lia|]. split; [reflexivity|].
    apply brk_r_ok_grow in Hr; [| fold h; lia| fold h; unfold PGSZ in *; lia]. fold h in Hr.
    dpose (brk_model_next_same h (Z_to_bv 64 req)) as (Q1 & Q2 & Q3 & Q4 & Q5).
    dpose (brk_model_next_grown h req ltac:(lia) ltac:(unfold PGSZ in *; lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct a.
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      { exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite Q5 in Ha.
        apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply brk_grow_ok_facts in Hgo; fold h in Hgo; [| fold h; lia| fold h; unfold PGSZ in *; lia| fold h; rewrite Ebrk; unfold PGSZ in *; rewrite Z.add_mod, R2, R4 by lia; reflexivity| subst req; unfold PGSZ in *; rewrite Z.add_mod, (Z.add_mod b l), R2, R4 by lia; reflexivity].
      ddestruct Hgo as (Hceil & Hrf & _). rewrite <- Kcl in Hceil.
      assert (HPG : lbrk_pages_ok L (b + l) PGSZ = true).
      { apply (KL_lbrk_pages_ok L (ps_brk s0) mo (b + l) PGSZ HK); [lia| unfold PGSZ; lia| subst req; lia| |].
        - replace (b + l) with (bv_unsigned (vm_brk h)) at 1 by exact Ebrk. replace (Z_to_bv 64 PGSZ) with (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) by (f_equal; lia). exact Hrf.
        - intros b1 l1 E. rewrite Ereg in E. injection E as <- <-. split; [exact R4| left; lia]. }
      rewrite Z_to_bv_bv_unsigned in Hrf.
      assert (Hn : bv_unsigned (Z_to_bv 64 (req - bv_unsigned (vm_brk h))) = PGSZ) by (rewrite unsigned_lit; unfold PGSZ in *; lia).
      pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
      split; [|exact HPG].
      kl_open HK. constructor; rewrite ?Emo'; cbn [m_vmmaps with_vmmaps set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil];
        rewrite ?P1, ?P2, ?P3, ?P4, ?P5; auto.
      + apply vmwf_cons; [exact Kwf| rewrite Hn; unfold PGSZ in *; lia| eapply region_free_app_r; exact Hrf].
      + rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; try lia; auto.
      + intros b0 l0 Hin. dpose (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kgr b0 l0 Hin). ddestruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G6 b l Ereg). clear -G6 D Ebrk B2. lia.
      + intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6).
        pose proof (region_free_disj _ _ _ _ (region_free_app_r _ _ _ _ Hrf) B4) as D. rewrite B5, B6, Hn in D.
        specialize (Kme b0 l0 k Hin). ddestruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption; try (right; assumption).
        unfold brk_disj in *. cbn. intros b1 l1 E. injection E as <- <-. specialize (G8 b l Ereg). clear -G8 D Ebrk B2. lia.
      + intros b1 l1 E. injection E as <- <-. splits; auto.
        * clear -R3. unfold PGSZ in *; lia.
        * unfold PGSZ in *. rewrite Z.add_mod, R4 by lia. reflexivity.
        * clear -Hceil. subst req. lia.
        * intros x Hx. destruct (Z_lt_le_dec x (b + l)) as [Hlt|Hge].
          -- ddestruct (Rcov x ltac:(lia)) as (e & He & Hr'). exists e. split; [right; exact He| exact Hr'].
          -- exists (vm_brk h, Z_to_bv 64 (req - bv_unsigned (vm_brk h))). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Hn. lia.
      + rewrite Hph. dexists b, (l + PGSZ). rewrite unsigned_lit by (unfold PGSZ in *; lia). splits; auto; lia.
    - (* [comment removed for export] *)
      destruct Hr as [-> | [-> Hgo]].
      2:{ exfalso. rewrite Emo' in Ha. cbn [m_vmmaps with_vmmaps] in Ha. rewrite P5 in Ha.
          apply (f_equal bv_unsigned) in Ha. rewrite unsigned_lit in Ha by (unfold PGSZ in *; lia). lia. }
      apply KL_dead with (pbrk := ps_brk s0). eapply KL_vm_eq; [exact HK| exact Hmi'| exact Hh'| | | | | |]; rewrite Emo'; cbn [m_vmmaps with_vmmaps]; first [assumption | reflexivity]. }
  intros a. cbn beta. destruct a.
  - eapply mspec_bind; [apply mspec_upd|]. intros []. apply mspec_ret.
    (intros s mo dd_H; ddestruct dd_H as (s1 & -> & -> & HGs & [Hne Hpos] & Ecur & HK)). unfold ev_step_post.
    cbn [ps_brk set_brk_ps ps_m ps_fa ps_so answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Z.eqb_refl.
    destruct HK as [HK HPG].
    splits; auto.
    + unfold brk_answer_ok. rewrite Z.eqb_refl, HPG. reflexivity.
    + eapply (HG s0); [reflexivity|reflexivity| apply vm_only_refl| exact HGs].
  - apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (-> & HGs & [Hne Hpos] & Ecur & HK)). unfold ev_step_post.
    cbn [answer_ok event_post].
    replace (req =? 0) with false by (symmetry; apply Z.eqb_neq; lia). rewrite Hph, Ereg, Ecur.
    replace (b + l =? req) with false by (symmetry; apply Z.eqb_neq; lia).
    splits; auto. unfold brk_answer_ok. rewrite Z.eqb_refl, orb_true_r. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma wcov_rf_disj : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Plo,$14.Phi,$14.Paw,(2.&40.)Pnw,(2.&40.)P,(1;.R5.R4.R3.)P,(5.$6.(7.R6.R3.R2.)$8.)P,(10.=(4.&40.R3.))P,(10.R7.R6.)(:.(3.(;.(4.&40.R6.)(4.&40.R5.))R8.)(3.R7.(4.&40.R6.)))")
(* [comment removed for export] *).
Proof.
  intros maps lo hi aw nw Hc Hrf Hn Hlh.
  destruct (Z_le_gt_dec (bv_unsigned aw + bv_unsigned nw) lo) as [|H1]; [left; assumption|].
  destruct (Z_le_gt_dec hi (bv_unsigned aw)) as [|H2]; [right; assumption|]. exfalso.
  ddestruct (Hc (Z.max (bv_unsigned aw) lo) ltac:(lia)) as (e & He & Hr).
  pose proof (region_free_disj _ _ _ _ Hrf He). lia.
Qed.


Lemma KL_mmap_new : forall L pbrk mo mo' a len (isnone : bool),
  KL L pbrk mo -> brk_quiet L -> 0 < len < LEN_MAX ->
  let h := m_vmmaps mo in let n := mmap_len len in
  mmap_addr_ok len [] a = true ->
  a + n <= alloc_top h ->    (* [comment removed for export] *)
  region_free (vm_reserved h ++ vm_maps h) (Z_to_bv 64 a) (Z_to_bv 64 n) = true ->
  minv mo' -> m_halted mo' = None ->
  m_vmmaps mo' = mkVmMapsFull (vm_reserved h) ((Z_to_bv 64 a, Z_to_bv 64 n) :: vm_maps h)
                 (if isnone then (Z_to_bv 64 a, Z_to_bv 64 n) :: vm_noaccess h else vm_noaccess h)
                 (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
  KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) pbrk mo'
  /\ mmap_answer_ok (ld_ceil L) (lranges L) len a = true /\ is_err a = false.
Proof.
  intros L pbrk mo mo' a len isnone HK Hq Hlen h n Hok A3 Hrf Hmi' Hh' Evm.
  pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl. pose proof (kl_ceil _ _ _ HK) as Kcl. fold h in Kcl. rewrite <- Kcl in A3.
  apply mmap_addr_ok_true in Hok as [(A1 & A2 & _) _]. rewrite page_size_eq in A1.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1. pose proof (mmap_len_pos_pg len ltac:(lia)) as Hn2. fold n in Hn1, Hn2.
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; lia).
  assert (Un : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  pose proof (region_free_app_r _ _ _ _ Hrf) as Hrfm.
  pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
  assert (Hround : round_up_pg len = n) by (subst n; apply round_up_pg_eq).
  (* [comment removed for export] *)
  assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                 a + n <= b0 \/ b0 + mmap_len l0 <= a).
  { intros b0 l0 H. dpose (WB b0 l0 H) as (B1 & B2 & B3 & B4 & B5 & B6).
    pose proof (region_free_disj _ _ _ _ Hrfm B4) as D. rewrite B5, B6, Ua, Un in D. exact D. }
  assert (Dbrk : forall b0 l0, ld_brkreg L = Some (b0, l0) -> a + n <= b0 + PGSZ \/ b0 + l0 <= a).
  { intros b0 l0 E. pose proof (kl_brkreg _ _ _ HK b0 l0 E) as (R1 & R2 & R3 & R4 & R5 & Rcov).
    pose proof (wcov_rf_disj _ _ _ _ _ Rcov Hrfm ltac:(rewrite Un; lia) ltac:(clear -R3; unfold PGSZ in *; lia)) as D. rewrite Ua, Un in D. exact D. }
  split; [|split].
  2:{ unfold mmap_answer_ok. apply orb_true_intro. right. rewrite Hround.
      rewrite (proj2 (Z.ltb_lt 0 a)) by lia. unfold PGSZ at 1. rewrite A1, Z.eqb_refl. rewrite (proj2 (Z.leb_le _ _) A3). cbn [andb].
      unfold ranges_free. apply forallb_forall. intros [lo m] Hin. cbn [fst snd]. unfold iv_disjoint.
      enough (a + n <= lo \/ lo + m <= a) as D.
      { destruct D as [D|D]; [rewrite (proj2 (Z.leb_le _ _) D); reflexivity| rewrite (proj2 (Z.leb_le _ _) D); apply orb_true_r]. }
      apply In_lranges in Hin as [H|[(b0 & l0 & H & E)|[(b0 & l0 & k & H & E)|(b0 & l0 & H & E)]]].
      - rewrite (kl_resv _ _ _ HK) in H. apply in_map_iff in H as ([e sz] & E & H). unfold wwZ in E. cbn [fst snd] in E. injection E as <- <-.
        pose proof (region_free_In _ _ _ _ _ Hrf (in_or_app _ _ _ (or_introl H))) as D. rewrite Ua, Un in D. exact D.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. left; exact H.
      - injection E as -> ->. rewrite round_up_pg_eq. fold (mmap_len l0). apply Dgm. right; exists k; exact H.
      - injection E as -> ->. pose proof (kl_brkreg _ _ _ HK b0 l0 H) as (R1 & R2 & R3 & R4 & R5 & _).
        rewrite round_up_pg_aligned by (unfold PGSZ in R4; exact R4). pose proof (Dbrk b0 l0 H). lia. }
  2:{ unfold is_err, TWO64. apply Z.ltb_ge. lia. }
  assert (Hnotin : ~ In a (map fst (ld_groups L) ++ map (fun m => fst (fst m)) (ld_metas L))).
  { intros Hin. apply in_app_or in Hin as [Hin|Hin].
    - apply in_map_iff in Hin as ([b0 l0] & E & Hin). cbn in E. subst b0.
      dpose (WB a l0 (or_introl Hin)) as (B1 & B2 & _). pose proof (Dgm a l0 (or_introl Hin)). lia.
    - apply in_map_iff in Hin as ([[b0 l0] k] & E & Hin). cbn in E. subst b0.
      pose proof (WB a l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & _). pose proof (Dgm a l0 (or_intror (ex_intro _ k Hin))). lia. }
  kl_open HK.
  assert (Hph' : forall L', ld_brk L' = ld_brk L -> ld_brkreg L' = ld_brkreg L ->
            match ld_brk L' with
            | BPUntried => vm_brk (m_vmmaps mo') = vm_start_brk (m_vmmaps mo') /\ ld_brkreg L' = None
            | BPQueried cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo')) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur /\ pbrk = cur /\ ld_brkreg L' = None
            | BPGuard cur => cur = bv_unsigned (vm_start_brk (m_vmmaps mo'))
                /\ bv_unsigned (vm_brk (m_vmmaps mo')) = cur + 2 * PGSZ /\ pbrk = cur + 2 * PGSZ
                /\ ld_brkreg L' = None /\ cur + 2 * PGSZ <= ld_ceil L'
                /\ (exists e, In e (vm_maps (m_vmmaps mo')) /\ elo e <= cur /\ cur + 2 * PGSZ <= ehi e)
                /\ (forall b l, In (b, l) (ld_groups L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
                /\ (forall b l k, In (b, l, k) (ld_metas L') -> b + mmap_len l <= cur \/ cur + 2 * PGSZ <= b)
            | BPLive => exists b l, ld_brkreg L' = Some (b, l) /\ bv_unsigned (vm_brk (m_vmmaps mo')) = b + l /\ pbrk = b + l
            | BPDead => True
            end).
  { intros L' E1 E2. rewrite E1, E2, Evm. cbn [vm_brk vm_start_brk]. unfold brk_quiet in Hq.
    destruct (ld_brk L); try contradiction; auto. }
  destruct isnone; constructor;
    first [ apply (Hph' (set_metas _ L)); reflexivity
          | apply (Hph' (set_groups _ L)); reflexivity
          | rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto ].
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 Hin. specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k [E|Hin].
    + injection E as <- <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
      * intros q Hq1 Hq2. exists (Z_to_bv 64 a, Z_to_bv 64 n). split; [left; reflexivity|]. rewrite elo_pair, ehi_pair, Ua, Un. fold n in Hq2. lia.
    + specialize (Kme b0 l0 k Hin). ddestruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
      intros q Hq1 Hq2. ddestruct (G9 q Hq1 Hq2) as (e & He & Hr). exists e. split; [right; exact He| exact Hr].
  - cbn [map fst app]. eapply Permutation_NoDup; [apply Permutation_middle|]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). ddestruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
  - apply vmwf_cons; [exact Kwf| rewrite Ua, Un; lia| exact Hrfm].
  - intros b0 l0 [E|Hin].
    + injection E as <- <-. unfold brk_disj; cbn. splits; try lia.
      * unfold PGSZ; exact A1.
      * left; reflexivity.
      * exact Dbrk.
    + specialize (Kgr b0 l0 Hin). unfold brk_disj in *; cbn. intuition auto with datatypes.
  - intros b0 l0 k Hin. specialize (Kme b0 l0 k Hin). ddestruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). unfold brk_disj in *; cbn. splits; try assumption; try (right; assumption).
  - cbn [map fst app]. constructor; [exact Hnotin| exact Kdis].
  - intros b0 l0 E. specialize (Kreg b0 l0 E). ddestruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto. eapply wcov_mono; [|exact Rcov]. intros e He; right; exact He.
Qed.

Lemma is_errno_form_neg : forall e, 1 <= e <= 4095 -> is_errno_form (neg_errno e) = true.
Proof. intros e He. unfold is_errno_form, neg_errno, TWO64. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity. Qed.
Lemma is_err_neg : forall e, 1 <= e <= 4095 -> is_err (neg_errno e) = true.
Proof. intros e He. unfold is_err, neg_errno, TWO64. apply Z.ltb_lt. lia. Qed.

Lemma ev_mmap_core : forall L G s0 len (isnone : bool), frame_ok G -> brk_quiet L -> 0 < len < LEN_MAX ->
  let prot := if isnone then PROT_NONE else PROT_RW in
  let dec := if isnone then dec_mmap_none len [] else dec_mmap len [] in
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo)
        (a <- msys (NMmap 0 len prot MAPF) dec ;; mret match a with MmErr e => neg_errno e | MmOk x => x end)
        (ev_step_post L (EMmap 0 len prot MAPF) G s0).
Proof.
  intros L G s0 len isnone HG Hq Hlen prot dec.
  pose proof (mmap_len_ge len ltac:(lia)) as Hn1.
  eapply mspec_bind.
  { apply (mspec_sys (NMmap 0 len prot MAPF) dec _
             (fun x s mo => s = s0 /\ G s mo /\
                match x with
                | MmErr e => e = ENOMEM /\ KL L (ps_brk s0) mo
                | MmOk a => KL (if isnone then set_metas ((a, len, 0) :: ld_metas L) L else set_groups ((a, len) :: ld_groups L) L) (ps_brk s0) mo
                            /\ mmap_answer_ok (ld_ceil L) (lranges L) len a = true /\ is_err a = false
                end)).
    (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). nsafe_assert.
    { subst prot. destruct isnone; [apply nsafe_mmap_none| apply nsafe_mmap_rw]; unfold LEN_MAX in *; lia. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    assert (Hcase : vm_only mo mo' /\ exists x, dec rsp = Some x /\
              match x with
              | MmErr e => e = ENOMEM /\ mo' = mo
              | MmOk a => mmap_addr_ok len [] a = true
                  /\ a + mmap_len len <= alloc_top (m_vmmaps mo)
                  /\ region_free (vm_reserved (m_vmmaps mo) ++ vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 (mmap_len len)) = true
                  /\ m_vmmaps mo' = mkVmMapsFull (vm_reserved (m_vmmaps mo)) ((Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_maps (m_vmmaps mo))
                       (if isnone then (Z_to_bv 64 a, Z_to_bv 64 (mmap_len len)) :: vm_noaccess (m_vmmaps mo) else vm_noaccess (m_vmmaps mo))
                       (vm_start_brk (m_vmmaps mo)) (vm_brk (m_vmmaps mo)) (vm_limit (m_vmmaps mo)) (vm_mmap_base (m_vmmaps mo)) (vm_init_sp (m_vmmaps mo))
              end).
    { subst prot dec. destruct isnone.
      - pose proof (nstep_dec_mmap_none len [] mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(unfold LEN_MAX in *; lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. exact Hx.
      - pose proof (nstep_dec_mmap len [] mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(unfold LEN_MAX in *; lia) (Forall_nil _) Hst) as (_ & Hvo & x & Hd & Hx).
        split; [exact Hvo|]. exists x. split; [exact Hd|]. exact Hx. }
    ddestruct Hcase as (Hvo & x & Hd & Hx). exists x. split; [exact Hd|].
    split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    destruct x as [e|a].
    - destruct Hx as [-> ->]. split; [reflexivity| exact HK].
    - ddestruct Hx as (Hok & Htop & Hrf & Evm). apply (KL_mmap_new L (ps_brk s0) mo mo' a len isnone HK Hq Hlen Hok Htop Hrf Hmi' Hh' Evm). }
  intros x. cbn beta. apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (-> & HGs & Hx)). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPF MAP_FIXED =? 0) with true. cbv iota.
  destruct x as [e|a].
  - destruct Hx as [-> HK]. rewrite is_err_neg by (unfold ENOMEM; lia).
    unfold mmap_answer_ok. rewrite is_errno_form_neg by (unfold ENOMEM; lia). splits; auto.
  - ddestruct Hx as (HK & Hans & Herr). rewrite Herr. subst prot. destruct isnone.
    + change (PROT_NONE =? PROT_NONE) with true. cbv iota. splits; auto.
    + change (PROT_RW =? PROT_NONE) with false. cbv iota. splits; auto.
Qed.

Lemma ev_mmap_ok : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.PG,P,$44.P,$1<.SpPs0,$44.Plen,$14.Pprot,$14.P,(45.R4.)P,(5>.R6.)P,(:.(5.$14.R3.$39.)(5.$14.R3.$5?.))P,(?.(10.=R5.)(10.R5.$60.))(48.$44.$14.Ls,$44.Lmo,$1<.(?.(5.$44.R2.R9.)(?.(3<.R;.(49.R2.)R1.)A2.R:.R2.R1.))(61.(62.=R6.R5.$63.))(51.R9.(62.=R6.R5.$63.)R8.R7.))")
(* [comment removed for export] *).
Proof.
  intros L G s0 len prot HG Hq Hprot Hlen. unfold ev_step.
  change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
  destruct Hprot as [-> | ->].
  - change (PROT_NONE =? 0) with true. cbv iota. apply (ev_mmap_core L G s0 len true HG Hq Hlen).
  - change (PROT_RW =? 0) with false. cbv iota. apply (ev_mmap_core L G s0 len false HG Hq Hlen).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma region_free_above : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Paw,(2.&40.)Pnw,(2.&40.)P,Pe,(1.(2.&40.)(2.&40.))P,(9.(1.(2.&40.)(2.&40.))R1.R4.)(3.(=.R2.)(4.&40.R4.))(5.$6.(7.R4.R3.R2.)$8.)")
(* [comment removed for export] *).
Proof.
  induction maps as [|[e sz] maps IH]; intros aw nw H; [reflexivity|]. cbn [region_free].
  rewrite IH by (intros e' He'; apply H; right; exact He'). unfold iv_overlap.
  specialize (H (e, sz) (or_introl eq_refl)). unfold ehi in H; cbn in H.
  replace (bv_unsigned aw <? bv_unsigned e + bv_unsigned sz) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.

Lemma ev_mmap_fixed_ok : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.PG,P,$44.P,$1<.SpPs0,$44.Pcur,$14.P,(45.R3.)P,(5.$41.(46.R5.)(64.R2.))Za,$14.(5:.R3.)(48.$44.$14.Ls,$44.Lmo,$1<.(?.(5.$44.R2.R7.)(?.(3<.R9.(49.R2.)R1.)A2.R8.R2.R1.))(61.(62.R1.$35.$39.$3:.))(51.R7.(62.R1.$35.$39.$3:.)R6.R5.))")
(* [comment removed for export] *).
Proof.
  intros L G s0 cur HG Hph a. unfold ev_step.
  change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
  set (L' := set_brkph BPLive (set_brkreg (Some (a, 2 * PGSZ)) L)).
  eapply mspec_bind.
  { apply (mspec_sys (NMmap a PGSZ PROT_NONE MAPFX) (dec_mmap_fixed a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with FxKept e => e = ENOMEM | FxDone => True | FxLost e => e = ENOMEM end)).
    (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl. pose proof (kl_ceil _ _ _ HK) as Kcl.
    pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. ddestruct Kph as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & Dg & Dm).
    pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4).
    assert (Ha : a = cur). { subst a. apply round_up_pg_aligned. rewrite Ecur. exact S2. }
    set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a). set (nw := Z_to_bv 64 PGSZ).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + PGSZ).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus, PGSZ in *. lia. }
    assert (Hrf : region_free (vm_reserved h) aw nw = true).
    { apply region_free_above. intros e He. rewrite Ua, Ha, Ecur. apply (kl_resv_top _ _ _ HK). exact He. }
    assert (Hmc : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists e0. split; [exact He0|]. rewrite Ua, Un. unfold elo, ehi in *.
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    assert (Hapos : 0 < a) by lia.
    assert (Htop : a + PGSZ <= alloc_top (m_vmmaps mo)) by (fold h; rewrite <- Kcl; lia).
    nsafe_assert.
    { apply nsafe_mmap_fixed; [exact Hapos| exact Htop| rewrite Ha, Ecur; exact S2| exact Hrf| exact Hmc]. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (nstep_mmap_fixed_inv a mo rsp mo' evs (kl_minv _ _ _ HK) Hapos Htop ltac:(rewrite Ha, Ecur; exact S2) Hrf Hmc Hst) as (_ & Hvo & x & Hd & Hx).
    fold h aw nw in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    (* [comment removed for export] *)
    pose proof (fun b0 l0 H => went_In_bounds _ _ _ b0 l0 HK H) as WB.
    assert (Dgm : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k, In (b0, l0, k) (ld_metas L)) ->
                   b0 + mmap_len l0 <= a \/ a + 2 * PGSZ <= b0).
    { intros b0 l0 [H|[k H]]; rewrite Ha; [apply (Dg _ _ H)| apply (Dm _ _ _ H)]. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> (ehi e <= a \/ a + PGSZ <= elo e) -> In e maps') ->
              (forall e, In e maps' -> In e (vm_maps h) \/ In e (maps_subtract (vm_maps h) a (a + PGSZ))) ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              (exists e', In e' maps' /\ elo e' <= a + PGSZ /\ a + 2 * PGSZ <= ehi e') ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hback Hna Hcov' Evm. subst L'.
      kl_open HK. constructor; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_brkph set_brkreg ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto.
      - intros b0 l0 Hin. dpose (WB b0 l0 (or_introl Hin)) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_introl Hin)) as D.
        specialize (Kgr b0 l0 Hin). ddestruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
      - intros b0 l0 k Hin. pose proof (WB b0 l0 (or_intror (ex_intro _ k Hin))) as (B1 & B2 & B3 & B4 & B5 & B6). pose proof (Dgm b0 l0 (or_intror (ex_intro _ k Hin))) as D.
        specialize (Kme b0 l0 k Hin). ddestruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact B4|]. rewrite B5, B6. clear -D. unfold PGSZ in *. lia.
        + unfold brk_disj; cbn. intros b1 l1 E. injection E as <- <-. clear -D. unfold PGSZ in *. lia.
        + intros q Hq1 Hq2. ddestruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - intros b1 l1 E. injection E as <- <-. splits.
        + lia.
        + rewrite Ha, Ecur. exact S2.
        + lia.
        + reflexivity.
        + lia.
        + intros z Hz. ddestruct Hcov' as (e' & He' & H1 & H2). exists e'. split; [exact He'|]. lia.
      - dexists a, (2 * PGSZ). splits; [reflexivity| lia| lia]. }
    assert (Hlohi : a < a + PGSZ) by (unfold PGSZ; lia). assert (Hhi : a + PGSZ < 2^64) by lia.
    destruct x as [e| |e].
    - destruct Hx as [-> ->]. split; [|reflexivity].
      apply (KLnew (vm_maps h) (vm_noaccess h)); auto.
      + exact (kl_wf _ _ _ HK).
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
      + subst h. destruct (m_vmmaps mo); reflexivity.
    - split; [|exact I].
      apply (KLnew (vm_maps h) ((aw, nw) :: maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
      + exact (kl_wf _ _ _ HK).
      + intros e x y He H1 H2 H3 H4. ddestruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi H1 H2 H3 H4) as (e' & He' & Hr).
        exists e'. split; [right; eapply maps_subtract_In_intro; eauto| exact Hr].
      + exists e0. split; [exact He0|]. unfold PGSZ in *; lia.
    - destruct Hx as [-> Evm]. split; [|reflexivity].
      apply (KLnew (maps_subtract (vm_maps h) a (a + PGSZ)) (maps_subtract (vm_noaccess h) a (a + PGSZ))); auto.
      + apply vmwf_subtract; [exact Hlohi| exact Hhi| exact (kl_wf _ _ _ HK)].
      + intros e He Hde. apply maps_subtract_keep; [exact (kl_wf _ _ _ HK)| exact Hlohi| exact He| exact Hde].
      + intros e x y He H1 H2 H3 H4. ddestruct (iv_subtract_contains (fst e) (snd e) a (a + PGSZ) x y Hlohi Hhi H1 H2 H3 H4) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      + ddestruct (iv_subtract_contains (fst e0) (snd e0) a (a + PGSZ) (a + PGSZ) (a + 2 * PGSZ) Hlohi Hhi ltac:(unfold elo in He0l; lia) ltac:(unfold PGSZ; lia) ltac:(unfold ehi in He0h; lia) ltac:(right; lia)) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr]. }
  intros x. cbn beta. apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (-> & HGs & HK & Hx)). unfold ev_step_post.
  cbn [answer_ok event_post]. change (Z.land MAPFX MAP_FIXED =? 0) with false. cbv iota. fold L'.
  splits; auto. unfold mmap_fixed_answer_ok. destruct x as [e| |e]; try subst e.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
  - rewrite Z.eqb_refl. apply orb_true_r.
  - rewrite is_errno_form_neg by (unfold ENOMEM; lia). reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma g_remove_split : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pa,$14.Pl0,$14.Pl,(0.(1.$14.$14.))PM,(0.$14.)P,(9.(1.$14.$14.)(13.$14.$14.R4.R3.)R2.)P,(65.$14.(34.$14.(66.(1.$14.$14.)$14.(18.$14.$14.)R3.)R2.))(17.(0.(1.$14.$14.))Ll1,(0.(1.$14.$14.))(17.(0.(1.$14.$14.))Ll2,(0.(1.$14.$14.))(?.(5.(0.(1.$14.$14.))R6.(34.(1.$14.$14.)R2.(12.(1.$14.$14.)(13.$14.$14.R8.R7.)R1.)))(5.(0.(1.$14.$14.))(67.R8.R6.)(34.(1.$14.$14.)R2.R1.)))))")
(* [comment removed for export] *).
Proof.
  intros a l0 l M. induction l as [|[x1 x2] l IH]; intros Hin Hnd; [destruct Hin|]. cbn [g_remove fst snd].
  cbn [map fst app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct (Z.eqb_spec x1 a) as [->|Hne].
  - destruct Hin as [E|Hin]; [injection E as ->; dexists [], l; split; reflexivity|].
    exfalso. apply Hni. apply in_or_app. left. apply in_map_iff. exists (a, l0). split; [reflexivity| exact Hin].
  - destruct Hin as [E|Hin]; [injection E; intros; subst; contradiction|]. ddestruct (IH Hin Hnd') as (l1 & l2 & -> & E).
    dexists ((x1, x2) :: l1), l2. rewrite E. split; reflexivity.
Qed.

Lemma phase_quiet : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.PL',$3;.Ppbrk,$14.Pmo,$1<.Pmo',$1<.P,(3<.R5.R3.R2.)P,(5>.R6.)P,(5.$41.(46.R6.)(46.R7.))P,(5.(3>.(1.$14.$14.))(5;.R7.)(5;.R8.))P,(5.(2.&40.)(2?.(22.R5.))(2?.(22.R6.)))P,(5.(2.&40.)(28.(22.R6.))(28.(22.R7.)))(42.(46.R:.)R:.R9.R7.)")
(* [comment removed for export] *).
Proof.
  intros L L' pbrk mo mo' HK Hq E1 E2 E3 E4. pose proof (kl_phase _ _ _ HK) as Kph. unfold brk_quiet in Hq. unfold phase_inv.
  rewrite E1, E2, E3, E4. destruct (ld_brk L); try contradiction; auto.
Qed.

Lemma ev_munmap_ok : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.PG,P,$44.P,$1<.SpPs0,$44.Pa,$14.Pl0,$14.Plen,$14.P,(45.R5.)P,(5>.R7.)P,(9.(1.$14.$14.)(13.$14.$14.R5.R4.)(53.R8.))P,(:.(5.$14.R4.R5.)(5.$14.R4.(5:.R5.)))(48.$44.$14.Ls,$44.Lmo,$1<.(?.(5.$44.R2.R:.)(?.(3<.R<.(49.R2.)R1.)A2.R;.R2.R1.))(61.(68.R7.R5.))(51.R:.(68.R7.R5.)R9.R8.))")
(* [comment removed for export] *).
Proof.
  intros L G s0 a l0 len HG Hq Hin Hlen. unfold ev_step.
  rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
  set (L' := set_groups (g_remove a (ld_groups L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMunmap a len) (dec_munmap a len) _
             (fun x s mo => s = s0 /\ G s mo /\ KL L' (ps_brk s0) mo /\ match x with RgErr e => e = EINVAL | RgDone _ => True end)).
    (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl. pose proof (kl_ceil _ _ _ HK) as Kcl.
    pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (went_In_bounds _ _ _ a l0 HK (or_introl Hin)) as (_ & B2 & _ & _ & B5 & B6).
    set (n := mmap_len l0) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 n) in *.
    assert (Hnn : mmap_len n = n) by (subst n; apply mmap_len_of_aligned; [lia| apply mmap_len_aligned]).
    assert (Hlen3 : 0 < len < 2^64 /\ mmap_len len = n).
    { destruct Hlen as [-> | ->]; [unfold LEN_MAX in A1; split; [lia| reflexivity]| split; [lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
    assert (Un : bv_unsigned nw = n) by (subst nw; apply unsigned_lit; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + n).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus. lia. }
    assert (Hhas : map_has (vm_maps h) aw nw = true).
    { unfold map_has. apply existsb_exists. exists (went a n). split; [exact A5|]. unfold went, wz. fold aw nw. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity. }
    nsafe_assert.
    { unfold nsafe, munmap_safe_b. fold h aw. rewrite Ua, page_size_eq. unfold PGSZ in A3. rewrite A3. rewrite w_is0_lit by lia.
      replace (len =? 0) with false by (symmetry; apply Z.eqb_neq; lia). cbn [negb orb Z.eqb]. cbv zeta.
      rewrite (unsigned_lit len) by lia. fold (mmap_len len). rewrite Hlen2. change (Z_to_bv 64 n) with nw.
      rewrite Hhas. destruct (TASK_SIZE <? a + n); reflexivity. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_munmap a len mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(lia) ltac:(lia) ltac:(rewrite Hlen2; lia) Hsafe Hst) as (_ & Hvo & x & Hd & Hx).
    rewrite Hlen2 in Hx. fold h aw nw in Hx.
    exists x. split; [exact Hd|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    (* [comment removed for export] *)
    pose proof (kl_distinct _ _ _ HK) as Kd.
    destruct (g_remove_split a l0 (ld_groups L) _ Hin Kd) as (g1 & g2 & Eg & Ezz).
    rewrite Eg, map_app in Kd. cbn [map fst] in Kd. rewrite <- app_assoc in Kd. cbn [app] in Kd.
    pose proof (List.NoDup_remove_1 _ _ _ Kd) as Kd1. pose proof (List.NoDup_remove_2 _ _ _ Kd) as Kd2.
    assert (Hg' : forall b l, In (b, l) (g_remove a (ld_groups L)) -> In (b, l) (ld_groups L) /\ b <> a).
    { intros b l H. rewrite Ezz in H. rewrite Eg. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]|].
      intros ->. apply Kd2. rewrite app_assoc, <- map_app. apply in_or_app. left. apply in_map_iff. exists (a, l). split; [reflexivity| exact H]. }
    assert (Hm' : forall b l k, In (b, l, k) (ld_metas L) -> b <> a).
    { intros b l k H ->. apply Kd2. apply in_or_app. right. apply in_or_app. right. apply in_map_iff. exists (a, l, k). split; [reflexivity| exact H]. }
    (* [comment removed for export] *)
    assert (Dother : forall b l, (In (b, l) (ld_groups L) \/ exists k, In (b, l, k) (ld_metas L)) -> b <> a ->
                     b + mmap_len l <= a \/ a + n <= b).
    { intros b l H Hne. pose proof (went_In_bounds _ _ _ b l HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (KLnew : forall maps' noacc',
              vmwf maps' ->
              (forall e, In e (vm_maps h) -> fst e <> aw -> In e maps') ->
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + n <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) maps' noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros maps' noacc' Hwf' Hkeep Hna Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      assert (Kfst : forall b l, b <> a -> 0 < b < 2^64 -> fst (went b (mmap_len l)) <> aw).
      { intros b l Hne Hb E. apply Hne. apply (f_equal bv_unsigned) in E. cbn [fst went] in E. rewrite unsigned_wz, Ua in E by lia. exact E. }
      subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_groups ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto.
      - intros b0 l1 Hin0. destruct (Hg' b0 l1 Hin0) as [Hin1 Hne]. specialize (Kgr b0 l1 Hin1). ddestruct Kgr as ([G0 G1] & G2 & G3 & G4 & G5 & G6). splits; try assumption.
        apply Hkeep; [exact G5|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
      - intros b0 l1 k Hin0. pose proof (Hm' b0 l1 k Hin0) as Hne. specialize (Kme b0 l1 k Hin0). ddestruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9). splits; try assumption.
        + apply Hkeep; [exact G7|]. apply Kfst; auto. pose proof (mmap_len_ge l1 G0). lia.
        + intros q Hq1 Hq2. ddestruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          pose proof (Dother b0 l1 (or_intror (ex_intro _ k Hin0)) Hne) as D.
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). clear -D Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite Ezz, map_app, <- app_assoc. exact Kd1.
      - intros b0 l1 E. specialize (Kreg b0 l1 E). ddestruct Kreg as (R1 & R2 & R3 & R4 & R5 & Rcov). splits; auto.
        intros z Hz. ddestruct (Rcov z Hz) as (e & He & Hr). exists e. split; [|exact Hr]. apply Hkeep; [exact He|].
        intros Efst. unfold brk_disj in A6. specialize (A6 b0 l1 E).
        destruct (pwdisj_In _ _ _ (proj2 Kwf) He A5) as [->|D].
        + rewrite B5, B6 in Hr. clear -Hr A6 Hz R3. unfold PGSZ in *. lia.
        + pose proof (proj1 Kwf e He) as W. unfold edisj, elo, ehi in D, W. rewrite Efst in D, W. cbn [fst snd went] in D. unfold wz in D. fold aw nw in D. rewrite Un in D. lia. }
    assert (Hlohi : bv_unsigned aw < bv_unsigned aw + bv_unsigned nw) by (rewrite Ua, Un; lia).
    assert (Hhi : bv_unsigned aw + bv_unsigned nw < 2^64) by (rewrite Ua, Un; lia).
    destruct x as [e|[|]].
    - destruct Hx as [-> ->]. split; [|reflexivity]. apply (KLnew (vm_maps h) (vm_noaccess h)).
      + exact (kl_wf _ _ _ HK).
      + auto.
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + subst h. destruct (m_vmmaps mo); reflexivity.
    - destruct Hx as [_ Evm]. split; [|exact I]. apply (KLnew (map_remove (vm_maps h) aw) (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))).
      + apply vmwf_remove. exact (kl_wf _ _ _ HK).
      + intros e He Hne. unfold map_remove. apply filter_In. split; [exact He|]. destruct (bv_eqb (fst e) aw) eqn:E; [|reflexivity]. apply bv_eqb_eq in E. contradiction.
      + intros e x y He H1 H2 H3 H4. ddestruct (iv_subtract_contains (fst e) (snd e) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) x y Hlohi Hhi H1 H2 H3 ltac:(rewrite Ua, Un; exact H4)) as (e' & He' & Hr).
        exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
      + exact Evm.
    - destruct Hx as [-> _]. split; [|exact I]. apply (KLnew (vm_maps h) (vm_noaccess h)).
      + exact (kl_wf _ _ _ HK).
      + auto.
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + subst h. destruct (m_vmmaps mo); reflexivity. }
  intros x. cbn beta. apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (-> & HGs & HK & Hx)). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'.
  splits; auto. unfold munmap_answer_ok. destruct x as [e|b]; try subst e.
  - rewrite is_errno_form_neg by (unfold EINVAL; lia). apply orb_true_r.
  - reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma nodup_map_inj : forall {A B} (f : A -> B) l x y, List.NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
Proof.
  induction l as [|z l IH]; intros x y Hnd Hx Hy E; [destruct Hx|]. cbn in Hnd. inversion Hnd; subst.
  destruct Hx as [<-|Hx], Hy as [<-|Hy]; [reflexivity| | | apply IH; auto].
  - exfalso. apply H1. rewrite E. apply in_map. exact Hy.
  - exfalso. apply H1. rewrite <- E. apply in_map. exact Hx.
Qed.

Lemma map_base_bump : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pa,$14.Pms,(0.(1.(1.$14.$14.)$14.))(5.(0.$14.)(66.(1.(1.$14.$14.)$14.)$14.Lm,(1.(1.$14.$14.)$14.)(18.$14.$14.(18.(1.$14.$14.)$14.R1.))(66.(1.(1.$14.$14.)$14.)(1.(1.$14.$14.)$14.)(69.R2.)R1.))(66.(1.(1.$14.$14.)$14.)$14.Lm,(1.(1.$14.$14.)$14.)(18.$14.$14.(18.(1.$14.$14.)$14.R1.))R1.))")
(* [comment removed for export] *).
Proof.
  intros a ms. rewrite map_map. apply map_ext. intros [[b l] k]. unfold bump_meta. destruct (_ =? _); reflexivity.
Qed.

(* [comment removed for export] *)
Lemma map_contains_not_free : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Pmaps,(0.(1.(2.&40.)(2.&40.)))Pa,(2.&40.)Pn,(2.&40.)P,(10.=(4.&40.R1.))P,(5.$6.(36.R4.R3.R2.)$8.)P,(5.$6.(7.R5.R4.R3.)$8.)$6:.")
(* [comment removed for export] *).
Proof.
  intros maps a n Hn Hc Hf. unfold map_contains in Hc. apply existsb_exists in Hc as ([e sz] & Hin & Hb).
  cbn [fst snd] in Hb. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (region_free_In _ _ _ _ _ Hf Hin). lia.
Qed.

Lemma nstep_mprotect_rgfalse : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Paddr,$14.Plen,$14.Pmo,$1<.Prsp,$1=.Pmo',$1<.Pevs,(0.$1>.)Zh,$21.(22.R4.)Za,(2.&40.)(24.&40.R7.)Zn,(2.&40.)(24.&40.(55.R7.))P,(3=.R7.)P,(?.(3.=R:.)(10.R:.(11.+2.+40.)))P,(10.=R:.)P,(10.(55.R;.)(11.+2.+40.))P,(37.(6;.R=.R<.(;.$6<.$6=.))R;.)P,(5.$6.(36.(2>.R8.)R7.R6.)$8.)P,(1?.(6;.R?.R>.(;.$6<.$6=.))R=.R<.R;.R:.)P,(5.(3>.$6>.)(6?.R10.R?.R=.)(5<.$6>.(70.$71.)))$6:.")
(* [comment removed for export] *).
Proof.
  intros addr len mo rsp mo' evs h a n Hm Ha Hlen Hlen2 Hs Hcn H Hd.
  pose proof (mmap_len_bound len Hlen) as Hb.
  ddestruct (nstep_dec_mprotect addr len mo rsp mo' evs Hm Ha Hlen Hlen2 Hs H) as (_ & _ & x & Hx & Hcase).
  rewrite Hd in Hx. injection Hx as <-. destruct Hcase as [_ Hrf].
  eapply map_contains_not_free; [| exact Hcn | exact Hrf]. unfold n. rewrite unsigned_lit by lia. lia.
Qed.

Lemma ev_mprotect_ok : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.PG,P,$44.P,$1<.SpPs0,$44.Pb,$14.Pl,$14.Pk,$14.P,(45.R5.)P,(5>.R7.)P,(9.(1.(1.$14.$14.)$14.)(13.(1.$14.$14.)$14.(13.$14.$14.R5.R4.)R3.)(54.R8.))P,(3.(72.(;.+2.R4.)$35.)(5:.R5.))Za,$14.(;.R7.(72.(;.+1.R5.)$35.))(48.$44.$14.Ls,$44.Lmo,$1<.(?.(5.$44.R2.R;.)(?.(3<.R=.(49.R2.)R1.)A2.R<.R2.R1.))(61.(73.R1.$35.$5?.))(51.R;.(73.R1.$35.$5?.)R:.R9.))")
(* [comment removed for export] *).
Proof.
  intros L G s0 b l k HG Hq Hin Hk2 a. unfold ev_step.
  rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
  set (L' := set_metas (map (bump_meta a) (ld_metas L)) L).
  eapply mspec_bind.
  { apply (mspec_sys (NMprotect a PGSZ PROT_RW) (dec_mprotect_rw a PGSZ) _
             (fun x s mo => s = s0 /\ G s mo /\ match x with RgErr e => (e = EINVAL \/ e = ENOMEM) /\ KL L (ps_brk s0) mo | RgDone _ => KL L' (ps_brk s0) mo end)).
    (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl. pose proof (kl_ceil _ _ _ HK) as Kcl.
    pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Uhi : bv_unsigned (aw + nw)%bv = a + PGSZ).
    { rewrite bv_add_unsigned, Ua, Un. apply bv_wrap_small. unfold bv_modulus, PGSZ in *. lia. }
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
    { ddestruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    nsafe_assert.
    { unfold nsafe, mprotect_safe_b. fold h aw nw.
      change (mprotect_grows_conflict_b (Z_to_bv 64 PROT_RW)) with false. change (mprotect_modeled_b (Z_to_bv 64 PROT_RW)) with true.
      rewrite Ua, page_size_eq, Hamod. change (w_is0 nw) with false. cbv iota. cbn [Z.eqb negb]. rewrite Un. change (page_round_up_Z PGSZ) with PGSZ.
      replace (two_pow_64 <=? a + PGSZ) with false by (symmetry; apply Z.leb_gt; unfold two_pow_64, PGSZ in *; lia). cbv zeta. fold nw. rewrite Hcn, Hcm. reflexivity. }
    intros rsp mo' evs Hst.
    pose proof (minv_preserved _ _ _ _ _ (kl_minv _ _ _ HK) (kl_halt _ _ _ HK) Hsafe Hst) as [Hh' Hmi'].
    pose proof (nstep_dec_mprotect a PGSZ mo rsp mo' evs (kl_minv _ _ _ HK) ltac:(unfold PGSZ in *; lia) ltac:(unfold PGSZ; lia) ltac:(change (mmap_len PGSZ) with PGSZ; unfold PGSZ; lia) Hsafe Hst) as (_ & Hvo & x & Hd & Hx).
    change (mmap_len PGSZ) with PGSZ in Hx. fold h aw nw in Hx.
    assert (HdRW : dec_mprotect_rw a PGSZ rsp = Some x).
    { destruct x as [e|[|]].
      - destruct Hx as [He _]. unfold dec_mprotect_rw. rewrite Hd.
        replace (e =? ENOSYS) with false by (symmetry; apply Z.eqb_neq; destruct He as [-> | ->]; unfold EINVAL, ENOMEM, ENOSYS; lia). reflexivity.
      - unfold dec_mprotect_rw. rewrite Hd. reflexivity.
      - exfalso. destruct Hx as [_ Hrf0]. eapply (map_contains_not_free _ aw nw); [rewrite Un; unfold PGSZ; lia| exact Hcn| exact Hrf0]. }
    exists x. split; [exact HdRW|]. split; [reflexivity|]. split; [eapply HG; [reflexivity|reflexivity| exact Hvo| exact HGs]|].
    pose proof (kl_distinct _ _ _ HK) as Kd. pose proof (List.NoDup_app_remove_l _ _ Kd) as Kdm.
    (* [comment removed for export] *)
    assert (Dother : forall b0 l0, (In (b0, l0) (ld_groups L) \/ exists k0, In (b0, l0, k0) (ld_metas L)) -> b0 <> b ->
                     b0 + mmap_len l0 <= b \/ b + nb <= b0).
    { intros b0 l0 H Hne. pose proof (went_In_bounds _ _ _ b0 l0 HK H) as (C1 & C2 & C3 & C4 & C5 & C6).
      destruct (pwdisj_In _ _ _ (proj2 (kl_wf _ _ _ HK)) C4 A5) as [E|D].
      - exfalso. apply Hne. apply (f_equal elo) in E. rewrite C5, B5 in E. exact E.
      - unfold edisj in D. rewrite C5, C6, B5, B6 in D. lia. }
    assert (KLnew : forall noacc',
              (forall e x y, In e (vm_noaccess h) -> elo e <= x -> x < y -> y <= ehi e -> (y <= a \/ a + PGSZ <= x) ->
                  exists e', In e' noacc' /\ elo e' <= x /\ y <= ehi e') ->
              m_vmmaps mo' = mkVmMapsFull (vm_reserved h) (vm_maps h) noacc' (vm_start_brk h) (vm_brk h) (vm_limit h) (vm_mmap_base h) (vm_init_sp h) ->
              KL L' (ps_brk s0) mo').
    { intros noacc' Hna Evm.
      assert (Hph' : phase_inv (ld_brk L') L' (ps_brk s0) mo') by (eapply phase_quiet; [exact HK| exact Hq| reflexivity| reflexivity| rewrite Evm; reflexivity| rewrite Evm; reflexivity]).
      subst L'. kl_open HK. constructor; try exact Hph'; rewrite ?Evm; cbn [vm_reserved vm_maps vm_noaccess vm_start_brk vm_brk set_metas ld_resv ld_groups ld_metas ld_brkreg ld_brk ld_live ld_ceil]; auto.
      - intros b0 l0 k0' Hin0. apply in_map_iff in Hin0 as ([[b1 l1] k0] & Eb & Hin1).
        specialize (Kme b1 l1 k0 Hin1). ddestruct Kme as ([G0 G1] & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9).
        unfold bump_meta in Eb. destruct (Z.eqb_spec (b1 + (1 + k0) * PGSZ) a) as [Ea|Na]; injection Eb as -> -> <-.
        + (* [comment removed for export] *)
          assert (Eb0 : b0 = b).
          { destruct (Z.eq_dec b0 b) as [E|Hne]; [exact E|]. exfalso.
            pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. pose proof (mmap_len_ge l0 G0). clear -D Ea Hab G5 G6 H. unfold PGSZ in *. nia. }
          subst b0. pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->.
          splits; try assumption; try lia.
          intros q Hq1 Hq2. ddestruct (G9 q ltac:(lia) Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b + q * PGSZ) (b + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh). right. subst a. clear -Hq1. unfold PGSZ in *. nia.
        + splits; try assumption.
          intros q Hq1 Hq2. ddestruct (G9 q Hq1 Hq2) as (e & He & Hel & Heh).
          apply (Hna e (b0 + q * PGSZ) (b0 + q * PGSZ + PGSZ) He Hel ltac:(unfold PGSZ; lia) Heh).
          destruct (Z.eq_dec b0 b) as [->|Hne].
          { pose proof (nodup_map_inj _ _ _ _ Kdm Hin1 Hin (eq_refl b)) as E. injection E as -> ->. exfalso. apply Na. reflexivity. }
          pose proof (Dother b0 l0 (or_intror (ex_intro _ k0 Hin1)) Hne) as D. clear -D Hab Hq1 Hq2 G5. unfold PGSZ in *. nia.
      - rewrite map_base_bump. exact Kd. }
    destruct x as [e|[|]].
    - destruct Hx as [He ->]. split; [exact He| exact HK].
    - ddestruct Hx as (_ & _ & Evm). apply (KLnew (maps_subtract (vm_noaccess h) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw))); [|exact Evm].
      assert (Hlohi : bv_unsigned aw < bv_unsigned aw + bv_unsigned nw) by (rewrite Ua, Un; unfold PGSZ; lia).
      assert (Hhi : bv_unsigned aw + bv_unsigned nw < 2^64) by (rewrite Ua, Un; unfold PGSZ in *; lia).
      intros e x y He H1 H2 H3 H4. ddestruct (iv_subtract_contains (fst e) (snd e) (bv_unsigned aw) (bv_unsigned aw + bv_unsigned nw) x y Hlohi Hhi H1 H2 H3 ltac:(rewrite Ua, Un; exact H4)) as (e' & He' & Hr).
      exists e'. split; [eapply maps_subtract_In_intro; eauto| exact Hr].
    - destruct Hx as [-> _]. apply (KLnew (vm_noaccess h)).
      + intros e x y He H1 H2 H3 H4. exists e. auto.
      + subst h. destruct (m_vmmaps mo); reflexivity. }
  intros x. cbn beta. apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (-> & HGs & Hx)). unfold ev_step_post.
  cbn [answer_ok event_post]. fold L'. unfold mprotect_answer_ok.
  destruct x as [e|bb].
  - destruct Hx as [He HK]. rewrite is_errno_form_neg by (destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? 0) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    replace (neg_errno e =? TWO64 - ENOSYS) with false by (symmetry; apply Z.eqb_neq; unfold neg_errno, TWO64, ENOSYS; destruct He as [-> | ->]; unfold EINVAL, ENOMEM; lia).
    cbn [orb]. splits; auto.
  - cbn [Z.eqb orb]. splits; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_step_spec : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PL,$3;.Pe,$74.PG,P,$44.P,$1<.SpPs0,$44.P,(45.R2.)P,(75.R5.R4.)(48.$44.$14.Ls,$44.Lmo,$1<.(?.(5.$44.R2.R5.)(?.(3<.R8.(49.R2.)R1.)A2.R6.R2.R1.))(61.R5.)(51.R6.R5.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros L e G s0 HG Hpre. destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - destruct Hpre as [[-> Hph]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]].
    + unfold ev_step. cbn [Z.eqb]. apply ev_brk0_ok; assumption.
    + destruct (Z.eqb_spec (round_up_pg cur + 2 * PGSZ) 0) as [E|NE].
      * (intros s mo dd_H; ddestruct dd_H as (-> & HK & _)). exfalso. pose proof (kl_phase _ _ _ HK) as Kph. rewrite Hph in Kph. destruct Kph as (Ecur & _).
        pose proof (kl_start _ _ _ HK) as (S1 & _). pose proof (round_up_pg_ge cur). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow1_ok; assumption.
    + destruct (Z.eqb_spec (b + l + PGSZ) 0) as [E|NE].
      * (intros s mo dd_H; ddestruct dd_H as (-> & HK & _)). exfalso. pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & _). unfold PGSZ in *. lia.
      * unfold ev_step. rewrite (proj2 (Z.eqb_neq _ _) NE). apply ev_brk_grow2_ok; assumption.
  - destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + apply ev_mmap_ok; assumption.
    + apply ev_mmap_fixed_ok; assumption.
  - ddestruct Hpre as (Hq & l0 & Hin & Hlen). apply (ev_munmap_ok L G s0 addr l0 len); assumption.
  - ddestruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk). apply (ev_mprotect_ok L G s0 b l k); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma membed_spec {R} : forall (t : stree ev Z R) (Post : mled -> R -> Prop) (G : PState -> Model -> Prop) L s0,
  frame_ok G -> ctree_ok L t Post ->
  mspec (fun s mo => s = s0 /\ KL L (ps_brk s) mo /\ G s mo) (membed t)
        (fun r s mo => exists L', cpath L t L' r /\ Post L' r /\ KL L' (ps_brk s) mo /\ G s mo
                       /\ ps_m s = ps_m s0 /\ ps_fa s = ps_fa s0 /\ ps_so s = ps_so s0).
Proof.
  intros t. induction t as [r|e k IH]; intros Post G L s0 HG Hok.
  - cbn [membed]. apply mspec_ret. (intros s mo dd_H; ddestruct dd_H as (-> & HK & HGs)). exists L.
    split; [constructor|]. cbn in Hok. splits; auto.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hk].
    eapply mspec_bind; [apply (ev_step_spec L e G s0 HG Hpre)|].
    intros z. unfold ev_step_post. apply mspec_pointwise. (intros s1 mo1 dd_H; ddestruct dd_H as (Hans & HK1 & HG1 & Hm & Hfa & Hso)).
    eapply mspec_conseq; [apply (IH z Post G (event_post L e z) s1 HG (Hk z Hans))| |].
    + intros s mo [-> ->]. auto.
    + (intros r s mo dd_H; ddestruct dd_H as (L' & Hp & HP & HK & HG' & Hm' & Hfa' & Hso')). exists L'. split; [econstructor; eauto|].
      splits; auto; congruence.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition OWN (X : list bptr) (G : PState -> Model -> Prop) : assn PState := ltac2:(CDefT.buildp (gd_tbl_KStep ()) "Ls,$44.Lmo,$1<.(?.(17.$3;.LL,$3;.(?.(76.(77.R3.)R1.)(?.(3<.R1.(49.R3.)R2.)(78.$79.(66.(1.$79.$14.)$79.(18.$79.$14.)O2.)(7:.R1.)))))(?.(65.$79.(66.(1.$79.$14.)$79.(18.$79.$14.)O2.))A2.O1.R2.R1.))")
(* [comment removed for export] *).

Lemma OWN_G : forall X G s mo, OWN X G s mo -> G s mo.
Proof. intros X G s mo [_ [_ H]]. exact H. Qed.

Lemma OWN_perm : forall X Y G s mo, Permutation X Y -> OWN X G s mo -> OWN Y G s mo.
Proof.
  (intros X Y G s mo HP dd_H; ddestruct dd_H as [(L & Hc & HK & Hi) [Hnd HG]]).
  assert (HP' : Permutation (map fst X) (map fst Y)) by (apply Permutation_map; exact HP).
  split; [|split; [|exact HG]].
  - exists L. split; [exact Hc|]. split; [exact HK|]. intros c Hc'. apply Hi.
    eapply Permutation_in; [apply Permutation_sym; exact HP'| exact Hc'].
  - eapply Permutation_NoDup; [exact HP'| exact Hnd].
Qed.

Lemma OWN_weakG : forall X G G' s mo, OWN X G s mo -> (G s mo -> G' s mo) -> OWN X G' s mo.
Proof. intros X G G' s mo [A [B C]] H. split; [exact A|]. split; [exact B|]. auto. Qed.

(* [comment removed for export] *)
Lemma OWN_other : ltac2:(CDefT.buildp (gd_tbl_KStep ()) "PX,(0.$7;.)PG,P,$44.P,$1<.SpPs,$44.Ps',$44.Pmo,$1<.P,(7<.R5.R4.R3.R1.)P,(5.$7=.(77.R3.)(77.R4.))P,(5.$14.(49.R4.)(49.R5.))P,A2.R7.R5.R4.(7<.R9.R8.R6.R5.)")
(* [comment removed for export] *).
Proof.
  (intros X G s s' mo dd_H; ddestruct dd_H as [(L & Hc & HK & Hi) [Hnd HG]]; intros Hm Hb HG'). split; [|split; [exact Hnd|exact HG']].
  exists L. rewrite Hm, Hb. auto.
Qed.

Lemma OWN_nodup : forall X G s mo, OWN X G s mo -> List.NoDup (map fst X).
Proof. intros X G s mo [_ [H _]]. exact H. Qed.

Lemma KL_set_live : forall L v pbrk mo, KL L pbrk mo -> KL (set_live v L) pbrk mo.
Proof. intros L v pbrk mo K. destruct K; constructor; cbn; auto. Qed.

Lemma event_post_live : forall L e z, ld_live (event_post L e z) = ld_live L.
Proof.
  intros L e z. destruct e; cbn; repeat (destruct (_ =? _)); try reflexivity;
  try (destruct (ld_brk L); try reflexivity; destruct (ld_brkreg L) as [[? ?]|]; reflexivity);
  try (destruct (is_err z); reflexivity); try (destruct (_ || _); reflexivity).
Qed.

Lemma cpath_live {R} : forall L (t : stree ev Z R) L' r, cpath L t L' r -> ld_live L' = ld_live L.
Proof. intros L t L' r H. induction H; [reflexivity|]. rewrite IHcpath. apply event_post_live. Qed.

Lemma aptr_eqb_eq : forall a b, aptr_eqb a b = true <-> a = b.
Proof.
  intros [a1 a2] [b1 b2]. unfold aptr_eqb. cbn. rewrite andb_true_iff, N.eqb_eq, Z.eqb_eq.
  split; [intros [-> ->]; reflexivity| intros H; inversion H; auto].
Qed.

Lemma in_ap_remove : forall x c l, In x l -> x <> c -> In x (ap_remove c l).
Proof.
  intros x c l. induction l as [|y l IH]; intros Hin Hne; [destruct Hin|].
  cbn. destruct (aptr_eqb y c) eqn:E.
  - apply aptr_eqb_eq in E. subst y. destruct Hin as [->|Hin]; [congruence| exact Hin].
  - destruct Hin as [->|Hin]; [left; reflexivity| right; apply IH; assumption].
Qed.

Lemma cmalloc_overflow : forall cs n, size_overflows n = true -> cmalloc cs n = SRet (strip cs, None).
Proof. intros cs n H. unfold cmalloc, malloc_core. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
