(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Lib Require Import Tac Image ZBridge SysStep Walk Arr.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import SFModel.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Malloc Require Import MallocKit_B3 F_ntf_F.
From OSSVerify.Proofs.zstd.huf_decompress.lib.Common Require Import RunDraw.
From OSSVerify.Proofs.zstd.huf_decompress.lib Require KReplay.
Ltac2 kr_t_F_ntf_H () := "C59OSSVerify5KrLib4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc7F_ntf_H8eh_freedC1?~~~~~~~~~~~~~~~c59OSSVerify5KrLib6Malloc7F_ntf_H8eh_availC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc<MallocKit_B3<lor_sxv_zeroC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free3sxvC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free9sxv_rangeC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Malloc=F_malloc_free;lor_range64C1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC59OSSVerify5KrLib4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC59OSSVerify5KrLib4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC59OSSVerify5KrLib4Spec6Malloc<okay_to_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00C59OSSVerify5KrLib4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C59OSSVerify5KrLib4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC59OSSVerify5KrLib4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC59OSSVerify5KrLib4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C59OSSVerify5KrLib4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC59OSSVerify5KrLib4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03C59OSSVerify5KrLib4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C59OSSVerify5KrLib4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~".
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CANSEC1. Context {rc : runConstT}.
Definition ntf_cond (st : mstate) (g : aptr) (i : Z) : bool :=
  let mr := get_meta_rec st g in
  (Z.lor (m_freed mr) (m_avail mr) + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g.

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
End POST.

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

Hypothesis EH : entry_hyps st g i.
Hypothesis LO : ATOP <= lo.
Hypothesis LOLE : lo <= bv_unsigned sp - 80.

Lemma maskw_zero : maskw = 0 <-> mask = 0.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_H ()) ["CANSEC1"; "ENTRY"] "p;2p;1p;4g0000j25Tg000mj14Tg001ej10Tg002]j41Tg003Yj43Tg004Uj42Tp,2stR0p,1gR1'5R2#4%02P0P1p,1iR2p,2EHR3C1P0P1P2P3C3C2o"). Qed.
Lemma maskw_range : 0 <= maskw < 2^64.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_H ()) ["CANSEC1"; "ENTRY"] "p;2p;1p;4g0000j25Tg000mj14Tg005Zj10Tg001ej12Tg006Wj11Tg007Zj43Tp,2stp,1g'5R0#4R1#0%20R0#0%11%10C3o"). Qed.

(* [comment removed for export] *)
Lemma ntf_cond_unfold :
  ntf_cond st g i = ((mask + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_H ()) ["CANSEC1"; "ENTRY"] "p;2p;1g0000j2;Tg000mj1:Tg001ej10Tg008_j21Tg009<j19Tg00:0j22Tg00:Mj13Tg00;Hj14Tg00<Bj25Tg00<_j26Tg00=\j27Tg00>:j28Tg00>Tp,2stR0p,1gR1';R2#:%02'1p,1i#9'2%32#4'51601'7'8o"). Qed.

Lemma okf_unfold :
  okay_to_free st g =
    if m_freeable mr =? 0 then false
    else if (48 <=? sc) || (get_stride mr <? UNIT * size_class sc) then true
    else if m_maplen mr =? 0 then true
    else if negb (optr_eqb (m_next mr) (Some g)) then true
    else if negb (is_bouncing sc st) then true
    else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_H ()) ["CANSEC1"; "ENTRY"] "p;2p;1g0000j2GTg00?4j1FTg00<Bj27Tg00?oj12Tg00@Tj10Tg00A9j11Tg00AWj1=Tg00BSj25Tg00C0j1:Tg00Ckj19Tg00Dfj23Tg00ECj24Tg00E`j28Tg00F=j1ETg00G6j1DTg00Gmj2CTg00HOj2>Tg00IHj16Tg00Ifj2?Tg00:Mj1@Tg00:0j2ATg00Jbj2BTg00=\j2<Tg00>:j2;Tg00>TR0P0P0p,2stR1p,1gR2'GR3#Fg00KXR4'7g00L6R5P0P0g00LVR6#2#0#0#0#0#1%=3R7'5%:3g00M;%97'3'4'8g00N0R8P0P0%E3/74P8P0P0%D3g00NP/C2'>#6P8P0P01?71#6P8P0P0%06R0#0#2#1%@3%16'AR6'31B17'5%20#0#0#1,46'<P8P5n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000';o"). Qed.

Ltac post_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].
End ENTRY.



End CANSEC1.
