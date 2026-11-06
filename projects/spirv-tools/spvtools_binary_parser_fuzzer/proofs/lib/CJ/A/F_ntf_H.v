(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import Tac Image ZBridge SysStep SFModel Arr.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Plain.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.A Require Import MallocKit_B3 F_ntf_F.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require KReplay.
Ltac2 kr_t_F_ntf_H () := "C69OSSVerify5KrLib2CJ4Spec6Malloc<get_meta_recC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7m_freedC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc7m_availC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lorC69OSSVerify5KrLib2CJ4Spec6Malloc3bitC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3addC69OSSVerify5KrLib2CJ4Spec6Malloc:m_last_idxC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc9mask_uptoC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3eqbC69OSSVerify5KrLib2CJ4Spec6Malloc<okay_to_freeC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4andbK47Corelib4Init5Logic2eq01I47Corelib4Init9Datatypes4bool00C69OSSVerify5KrLib2CJ4Spec6Malloc:m_freeableC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums1Z02C69OSSVerify5KrLib2CJ4Spec6Malloc;m_sizeclassC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3lebC69OSSVerify5KrLib2CJ4Spec6Malloc:get_strideC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc:size_classC1?~~~~~~~~~~~~~~~C56Stdlib6ZArith6BinInt1Z3mulC56Stdlib6ZArith6BinInt1Z3ltbC47Corelib4Init9Datatypes3orbC69OSSVerify5KrLib2CJ4Spec6Malloc8m_maplenC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc6m_nextC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes6option01C69OSSVerify5KrLib2CJ4Spec6Malloc8optr_eqbC1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes4negbC69OSSVerify5KrLib2CJ4Spec6Malloc;is_bouncingC1?~~~~~~~~~~~~~~~C69OSSVerify5KrLib2CJ4Spec6Malloc5usageC1?~~~~~~~~~~~~~~~K47Corelib7Numbers7BinNums1Z01K47Corelib4Init9Datatypes4bool02K47Corelib7Numbers7BinNums8positive03C69OSSVerify5KrLib2CJ4Spec6Malloc4UNITC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4bool01C69OSSVerify5KrLib2CJ4Spec6Malloc4aptrC1?~~~~~~~~~~~~~~~".
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Definition ntf_cond (st : mstate) (g : aptr) (i : Z) : bool :=
  let mr := get_meta_rec st g in
  (Z.lor (m_freed mr) (m_avail mr) + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g.

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
Definition AT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs).

Definition entry_cases (ms' : machine_state) : Prop :=

  (ntf_cond st g i = false /\ mask <> 0 /\
   exists t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15e1c (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 SELF G a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = false /\ mask = 0 /\
   exists t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15dd4 (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 sc) SELF G a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = false /\ mask = 0 /\ active st sc = Some g /\
   exists t0 t1 t2 a0 a3 a4 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15e1c (mkR ra sp' gp tp t0 t1 t2 s0 s1 a0 SELF G a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ m_next mr = None /\ sc < 48 /\
   exists t0 t2 a3 a5 a6 t3 t4 t5 t6,
     AT 0x15b80 (mkR ra sp' gp tp t0 (Z_to_bv 64 sc) t2 s0 s1 (Z_to_bv 64 sc) SELF G a3 (Z_to_bv 64 CTX) a5 a6 (Z_to_bv 64 (m_last_idx mr)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ m_next mr = None /\ 48 <= sc /\
   exists t0 t2 a3 a5 a7 t3 t4 t5 t6,
     AT 0x15ba0 (mkR ra sp' gp tp t0 (Z_to_bv 64 sc) t2 s0 s1 (Z_to_bv 64 sc) SELF G a3 (Z_to_bv 64 CTX) a5 (Z_to_bv 64 (meta_word mr)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ m_next mr = Some g /\ sc < 48 /\
   exists t0 t1 t2 a5 a6 a7 t3 t4 t5 t6,
     AT 0x15c70 (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sc + 10)) SELF G HD (Z_to_bv 64 CTX) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) ms')
  \/
  (ntf_cond st g i = true /\ sc < 48 /\
   exists nx, m_next mr = Some nx /\ nx <> g /\
   exists t0 t1 t2 a5 a6 a7 t3 t4 t6,
     AT 0x15b38 (mkR ra sp' gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (sc + 10)) SELF G HD (Z_to_bv 64 CTX) a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 (conc st nx)) t6) ms').
End POST.

Definition entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists m1 junk,
    entry_cases ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st g i m1 ms'
    /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
    /\ stk asegs m1 lo (bv_unsigned sp + -80)
    /\ rw_cells asegs m1 (bv_unsigned sp + -80) [CB 72 junk; C8 ra]
    /\ mrep st m1.

Record entry_hyps (st : mstate) (g : aptr) (i : Z) : Prop := mkEH {
  eh_slot : meta_slot st g;
  eh_mw : mw_ok (get_meta_rec st g);
  eh_avail : 0 <= m_avail (get_meta_rec st g) < 2^32;
  eh_freed : 0 <= m_freed (get_meta_rec st g) < 2^32;
  eh_i : 0 <= i <= m_last_idx (get_meta_rec st g);

  eh_sc : m_sizeclass (get_meta_rec st g) < 48 \/ m_sizeclass (get_meta_rec st g) = 63;

  eh_next : forall nx, m_next (get_meta_rec st g) = Some nx -> meta_slot st nx;
  eh_head : forall h, active st (m_sizeclass (get_meta_rec st g)) = Some h -> meta_slot st h;
  eh_ctx : (forall j, 0 <= bounces st j < 256) /\ (m_sizeclass (get_meta_rec st g) < 48 -> 0 <= usage st (m_sizeclass (get_meta_rec st g)) < 2^64);

  eh_g50 : ntf_cond st g i = true -> m_next (get_meta_rec st g) <> None -> m_sizeclass (get_meta_rec st g) < 48;
  eh_g51 : ntf_cond st g i = false -> Z.lor (m_freed (get_meta_rec st g)) (m_avail (get_meta_rec st g)) = 0 -> m_sizeclass (get_meta_rec st g) < 48;

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

Definition mid_ctx (m1 : word -> option byte) (junk : list byte) : Prop :=
  munch [(bv_unsigned sp - 80, bv_unsigned sp)] m m1 /\ wmono asegs m m1 /\ mem_inv asegs m1
  /\ stk asegs m1 lo (bv_unsigned sp + -80) /\ rw_cells asegs m1 (bv_unsigned sp + -80) [CB 72 junk; C8 ra] /\ mrep st m1.

Lemma ntf_cond_unfold :
  ntf_cond st g i = ((mask + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g)%bool.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_H ()) ["AC_1"; "ENTRY"] "p;2p;1g0000j2;Tg0010j1:Tg001kj10Tg002fj21Tg003Cj19Tg004:j22Tg004Wj13Tg005Uj14Tg006Rj25Tg006oj26Tg007oj27Tg008Mj28Tg008gp,2stR0p,1gR1';R2#:%02'1p,1i#9'2%32#4'51601'7'8o"). Qed.

Lemma okf_unfold :
  okay_to_free st g =
    if m_freeable mr =? 0 then false
    else if (48 <=? sc) || (get_stride mr <? UNIT * size_class sc) then true
    else if m_maplen mr =? 0 then true
    else if negb (optr_eqb (m_next mr) (Some g)) then true
    else if negb (is_bouncing sc st) then true
    else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false.
Proof.
ltac2:(KReplay.run1 (kr_t_F_ntf_H ()) ["AC_1"; "ENTRY"] "p;2p;1g0000j2GTg009Gj1FTg006Rj27Tg00:Ej12Tg00:jj10Tg00;Oj11Tg00;mj1=Tg00<lj25Tg00=Ij1:Tg00>Gj19Tg00?Ej23Tg00?bj24Tg00@?j28Tg00@\j1ETg00AXj1DTg00BRj2CTg00C4j2>Tg00D0j16Tg00DNj2?Tg004Wj1@Tg004:j2ATg00EMj2BTg007oj2<Tg008Mj2;Tg008gR0P0P0p,2stR1p,1gR2'GR3#Fg00FFR4'7g00FdR5P0P0g00GDR6#2#0#0#0#0#1%=3R7'5%:3g00Gi%97'3'4'8g00HaR8P0P0%E3/74P8P0P0%D3g00IA/C2'>#6P8P0P01?71#6P8P0P0%06R0#0#2#1%@3%16'AR6'31B17'5%20#0#0#1,46'<P8P5n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000n0100000020000';o"). Qed.

Ltac post_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].

End ENTRY.

End AC_1.
