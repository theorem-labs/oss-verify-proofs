(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep MallocKit_B.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_MallocModel_B () := "C35stdpp6option;from_optionC47Corelib4Init9Datatypes2IDC59OSSVerify5KrLib4Spec6Malloc1MC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc>activate_groupC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5m_memC1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes4prod00C47Corelib4Init9Datatypes2idK47Corelib7Numbers7BinNums1Z03K47Corelib4Init9Datatypes4prod01C59OSSVerify5KrLib4Spec6Malloc@group_active_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z4landC56Stdlib6ZArith6BinInt1Z5ldiffC59OSSVerify5KrLib4Spec6Malloc;m_set_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc;m_set_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc8upd_metaC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1Z02K59OSSVerify5KrLib4Spec6Malloc<undef_reason01C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec6Malloc2ev06C1?~~~~~~~~~~~~~~~K59OSSVerify5KrLib4Spec5STree5stree02C1?~~~~~~~~~~~~~~~K47Corelib4Init5Logic2eq01C47Corelib4Init5Logic8eq_ind_rc59OSSVerify5KrLib6Malloc=MallocModel_B6act_ofC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=MallocModel_B6act_stC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc6mstate00C1?~~~~~~~~~~~~~~~I47Corelib7Numbers7BinNums1Z00K47Corelib7Numbers7BinNums1Z01I47Corelib4Init9Datatypes4bool00I59OSSVerify5KrLib4Spec6Malloc4meta00C1?~~~~~~~~~~~~~~~I47Corelib4Init9Datatypes6option00I47Corelib7Numbers7BinNums1N00K47Corelib7Numbers7BinNums1N01K47Corelib7Numbers7BinNums8positive03I59OSSVerify5KrLib4Spec6Malloc2ev00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=MallocModel_B7deq_midC1?~~~~~~~~~~~~~~~I59OSSVerify5KrLib4Spec6Malloc5lhead00C1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc=MallocModel_B9clr_linksC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition aor_st (st : mstate) (g : aptr) (i : Z) : mstate :=
  upd_meta g (fun r => m_set_freed (Z.lor (m_freed r) (bit i)) r) st.

(* [comment removed for export] *)
Definition act_st (st : mstate) (a : aptr) (act : Z) : mstate :=
  upd_meta a (fun r => m_set_avail (Z.land (m_freed r) act) (m_set_freed (Z.ldiff (m_freed r) act) r)) st.
Definition act_of (st : mstate) (a : aptr) : Z :=
  match m_mem (get_meta_rec st a) with
  | Some _ => mask_upto (group_active_idx st (default (0%N, -1) (m_mem (get_meta_rec st a))))
  | None => 0 end.

Lemma activate_group_eq {R} a st (k : mstate -> Z -> M R) bail :
  m_avail (get_meta_rec st a) = 0 ->
  activate_group a st k bail = k (act_st st a (act_of st a)) (Z.land (m_freed (get_meta_rec st a)) (act_of st a)).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocModel_B ()) ["CANSEC1"] "p'0h01rh11Rh21ai001ah34bailh41kh52sth61Hh71zi012a0i021ci031xp;1p;2p;3p;4p;5p;6p-1R0g0000R1p4p710p8P0P1p4p7210p8P0p1000Kp5p710p8p200R0g000gR2p4p710p8P0g001YR3p4p710p8P2j11Tg002Xj22Tg003Uj1=Tg004Mj35Tg004gj2LTg005Dj13Tg006<j14Tg0072j2BTg007Rj1@Tg007nj1?Tg008Lj4>TP1j59Tg008lj2:Tg009mj1<Tg00:gj20Tg00;Ej28Tg00;dj2;Tg00<`j27Tg00=\j36Tg00>Uj1KTg00?:j1JTg00?Xj1ITg00@Wj1ATg00ALj5CTg00BCj2DTg00B]j6ETP3j5FTg00C;j2GTg00D;j3HTg00E;R3g00F0R1g00FiR2f4R4#1[\1R5f3R6#1R7f2R8/26#=g00GGR9552P2P9f6R:#1g00Gef7R;#1f0R</L9P6f5R=g00HER>12=:R?#3R@g00I<RAP3P2%4?R?g00I^RB/B2RCPC%@CRDPBP2g00J<g00JZRB#?C>RE12:;#4D9,::#<R;P9n10110300021010000RF'018@F/;<'7W0;64124=RF#3R@PAP3P2%4FRFPCPCPDPEP?D9,:=#<RGP9n10110300021010000'0O2g00K?P2P:%KB#J#I#AP6V2DCn0110200020000P6%3<RBPAP3P2P?P;P9n10110300021010100R;'018B;/;<'7X0>=6=4PAP3P2PFPGP9n10110300021010100RG,0@O235X72%1=R@P810BG18BG/;<'7X0>=6461264R>#3RGPAP3P2%4>PCPCPDPEPFD9,:4#<P9n10110300021010100'0O2'D%=>P<EEP=P4P6P8f1R=DFP81G64R>9H6410G>O255@eW6X37X45X51X23X10P4P6P8P=P<O5W3W4W5W2X10o"). Qed.

(* [comment removed for export] *)
Definition deq_mid (h : lhead) (g : aptr) (st : mstate) : mstate :=
  let mr := get_meta_rec st g in
  if negb (optr_eqb (m_next mr) (Some g)) then
    let st1 := match m_prev mr with Some pv => upd_meta pv (m_set_next (m_next mr)) st | None => st end in
    let st2 := match m_next mr with Some nx => upd_meta nx (m_set_prev (m_prev mr)) st1 | None => st1 end in
    if optr_eqb (get_head st2 h) (Some g) then set_head h (m_next mr) st2 else st2
  else set_head h None st.
Definition clr_links (r : meta) : meta := m_set_prev None (m_set_next None r).
Lemma dequeue_mid : forall h g st, dequeue h g st = upd_meta g clr_links (deq_mid h g st).
Proof.
ltac2:(KReplay.run1 (kr_t_MallocModel_B ()) ["CANSEC1"] "h01gh11hh22stp;3p;2g00L4j32Tg00=\j31Tg00BCj20Tg00M5g00E;g00F0R0f1R1g00Mmf2f072131,00W2W0W1o"). Qed.

(* [comment removed for export] *)
Definition pd_st (an : bool) (st1 : mstate) (sc : Z) : mstate :=
  if an then match active st1 sc with Some a => act_st st1 a (act_of st1 a) | None => st1 end else st1.

(* [comment removed for export] *)
Definition grp_del (st : mstate) (g p : aptr) : mstate :=
  del_slots p (get_stride (get_meta_rec st g)) (m_last_idx (get_meta_rec st g) + 1) (del_group p st).
Definition fg_usage_st (st : mstate) (g : aptr) : mstate :=
  let mr := get_meta_rec st g in
  if m_sizeclass mr <? 48 then set_usage (m_sizeclass mr) (usage st (m_sizeclass mr) - (m_last_idx mr + 1)) st else st.


End CANSEC1.
