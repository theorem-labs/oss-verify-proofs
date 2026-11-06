(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B MallocModel_B F_ntf_A F_ntf_B F_ntf_C.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_B3 F_ntf_F.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_ntf_H () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.meta"; "OSSVerify.KrLib.Heap.Malloc.get_meta_rec"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.eqb"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.lor"; "OSSVerify.KrLib.Heap.Malloc.m_freed"; "OSSVerify.KrLib.Heap.Malloc.m_avail"; "OSSVerify.KrLib.Heap.Malloc.bit"; "OSSVerify.KrLib.Heap.Malloc.mask_upto"; "OSSVerify.KrLib.Heap.Malloc.m_last_idx"; "OSSVerify.KrLib.Heap.Malloc.okay_to_free"; "Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "ntf_cond"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Logic.not"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "POST.AT"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Heap.MallocRep.wz"; "OSSVerify.KrLib.Heap.F_malloc_free.sxv"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.Malloc.conc"; "OSSVerify.KrLib.Heap.Malloc.m_sizeclass"; "OSSVerify.KrLib.Heap.Malloc.optr"; "OSSVerify.KrLib.Heap.Malloc.active"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Heap.Malloc.m_next"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.MallocRep.CTX"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.MallocRep.meta_word"; "OSSVerify.KrLib.Heap.MallocRep.pw"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "entry_cases"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "OSSVerify.KrLib.Heap.MallocRep.mrep"].


(* [comment removed for export] *)
Definition ntf_cond (st : mstate) (g : aptr) (i : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_F_ntf_H ()) "Zmr,$0.(1.O3.O2.)(2.(3.(4.(5.(6.R1.)(7.R1.))(8.O1.))(9.(:.R1.)))(;.O3.O2.))")
(* [comment removed for export] *).

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
Definition AT (pc : Z) (R : bvmap 5 word) (ms' : machine_state) : Prop := ms' = MS R F (Z_to_bv 64 pc) fc None m1 (seg_rom asegs).

Definition entry_cases (ms' : machine_state) : Prop := ltac2:(CDefT.buildp (gd_tbl_F_ntf_H ()) "(<.(=.(>.$?.(10.Vst,Vg,Vi,)$11.)(=.(12.(>.$13.(5.(6.(1.Vst,Vg,))(7.(1.Vst,Vg,)))=))(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt1,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La0,(15.&40.)(14.(15.&40.)La3,(15.&40.)(14.(15.&40.)La4,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(16.+15>1<.(17.Vra,(18.&40.(4.(19.&40.Vsp,)-50.))Vgp,Vtp,R=.R<.R;.Vs0,Vs1,R:.(1:.(1;.(1<.+2.Vi,)))(18.&40.(1=.Vst,Vg,))R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.))))))))))))))))(<.(=.(>.$?.(10.Vst,Vg,Vi,)$11.)(=.(>.$13.(5.(6.(1.Vst,Vg,))(7.(1.Vst,Vg,)))=)(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt1,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La3,(15.&40.)(14.(15.&40.)La4,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(16.+15==4.(17.Vra,(18.&40.(4.(19.&40.Vsp,)-50.))Vgp,Vtp,R<.R;.R:.Vs0,Vs1,(18.&40.(1>.(1.Vst,Vg,)))(1:.(1;.(1<.+2.Vi,)))(18.&40.(1=.Vst,Vg,))R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))))(<.(=.(>.$?.(10.Vst,Vg,Vi,)$11.)(=.(>.$13.(5.(6.(1.Vst,Vg,))(7.(1.Vst,Vg,)))=)(=.(>.$1?.(20.Vst,(1>.(1.Vst,Vg,)))(21.$22.Vg,))(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt1,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La0,(15.&40.)(14.(15.&40.)La3,(15.&40.)(14.(15.&40.)La4,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(16.+15>1<.(17.Vra,(18.&40.(4.(19.&40.Vsp,)-50.))Vgp,Vtp,R=.R<.R;.Vs0,Vs1,R:.(1:.(1;.(1<.+2.Vi,)))(18.&40.(1=.Vst,Vg,))R9.R8.R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))))))(<.(=.(>.$?.(10.Vst,Vg,Vi,)$23.)(=.(>.$1?.(24.(1.Vst,Vg,))(25.$22.))(=.(26.(1>.(1.Vst,Vg,))+30.)(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La3,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(16.+15;80.(17.Vra,(18.&40.(4.(19.&40.Vsp,)-50.))Vgp,Vtp,R9.(18.&40.(1>.(1.Vst,Vg,)))R8.Vs0,Vs1,(18.&40.(1>.(1.Vst,Vg,)))(1:.(1;.(1<.+2.Vi,)))(18.&40.(1=.Vst,Vg,))R7.(18.&40.$27.)R6.R5.(18.&40.(:.(1.Vst,Vg,)))Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))(<.(=.(>.$?.(10.Vst,Vg,Vi,)$23.)(=.(>.$1?.(24.(1.Vst,Vg,))(25.$22.))(=.(28.+30.(1>.(1.Vst,Vg,)))(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La3,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(16.+15;:0.(17.Vra,(18.&40.(4.(19.&40.Vsp,)-50.))Vgp,Vtp,R9.(18.&40.(1>.(1.Vst,Vg,)))R8.Vs0,Vs1,(18.&40.(1>.(1.Vst,Vg,)))(1:.(1;.(1<.+2.Vi,)))(18.&40.(1=.Vst,Vg,))R7.(18.&40.$27.)R6.(18.&40.(29.(1.Vst,Vg,)))R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.)))))))))))))(<.(=.(>.$?.(10.Vst,Vg,Vi,)$23.)(=.(>.$1?.(24.(1.Vst,Vg,))(21.$22.Vg,))(=.(26.(1>.(1.Vst,Vg,))+30.)(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt1,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt5,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(16.+15<70.(17.Vra,(18.&40.(4.(19.&40.Vsp,)-50.))Vgp,Vtp,R:.R9.R8.Vs0,Vs1,(18.&40.(4.(1>.(1.Vst,Vg,))+:.))(1:.(1;.(1<.+2.Vi,)))(18.&40.(1=.Vst,Vg,))(2:.Vst,(20.Vst,(1>.(1.Vst,Vg,))))(18.&40.$27.)R7.R6.R5.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R4.R3.R2.R1.)O1.))))))))))))))(=.(>.$?.(10.Vst,Vg,Vi,)$23.)(=.(26.(1>.(1.Vst,Vg,))+30.)(14.$22.Lnx,$22.(=.(>.$1?.(24.(1.Vst,Vg,))(21.$22.R1.))(=.(12.(>.$22.R1.Vg,))(14.(15.&40.)Lt0,(15.&40.)(14.(15.&40.)Lt1,(15.&40.)(14.(15.&40.)Lt2,(15.&40.)(14.(15.&40.)La5,(15.&40.)(14.(15.&40.)La6,(15.&40.)(14.(15.&40.)La7,(15.&40.)(14.(15.&40.)Lt3,(15.&40.)(14.(15.&40.)Lt4,(15.&40.)(14.(15.&40.)Lt6,(15.&40.)(16.+15;38.(17.Vra,(18.&40.(4.(19.&40.Vsp,)-50.))Vgp,Vtp,R9.R8.R7.Vs0,Vs1,(18.&40.(4.(1>.(1.Vst,Vg,))+:.))(1:.(1;.(1<.+2.Vi,)))(18.&40.(1=.Vst,Vg,))(2:.Vst,(20.Vst,(1>.(1.Vst,Vg,))))(18.&40.$27.)R6.R5.R4.Vs2,Vs3,Vs4,Vs5,Vs6,Vs7,Vs8,Vs9,Vs10,Vs11,R3.R2.(18.&40.(1=.Vst,R:.))R1.)O1.)))))))))))))))))))))")
(* [comment removed for export] *).
End POST.

Definition entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : mstate) (g : aptr) (i lo : Z) (m : word -> option byte) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_F_ntf_H ()) "Lms',$2;.(14.P,(15.&40.)(2<.(15.&8.))Lm1,P,(15.&40.)(2<.(15.&8.))(14.(2=.(15.&8.))Ljunk,(2=.(15.&8.))(=.(2>.O17.O16.O15.O14.O13.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.O5.O4.O3.R2.R3.)(=.(2?.(30.(31.$13.$13.)(32.$13.$13.(33.(19.&40.O16.)+50.)(19.&40.O16.))(34.(31.$13.$13.)))O1.R2.)(=.(35.$36.O1.R2.)(=.(37.$36.R2.)(=.(38.$36.R2.O2.(4.(19.&40.O16.)-50.))(=.(39.$36.R2.(4.(19.&40.O16.)-50.)(30.$3:.(3;.#48.R1.)(30.$3:.(3<.O17.)(34.$3:.))))(3=.O5.R2.)))))))))")
(* [comment removed for export] *).

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
Hypothesis LO : ALLOC_CEIL_LO <= lo.   (* [comment removed for export] *)
Hypothesis LOLE : lo <= bv_unsigned sp - 80.


(* [comment removed for export] *)
#[using="Type"] Lemma ntf_cond_unfold :
  ntf_cond st g i = ((mask + bit i =? mask_upto (m_last_idx mr)) && okay_to_free st g)%bool.
Proof. reflexivity. Qed.

#[using="Type"] Lemma okf_unfold :
  okay_to_free st g =
    if m_freeable mr =? 0 then false
    else if (48 <=? sc) || (get_stride mr <? UNIT * size_class sc) then true
    else if m_maplen mr =? 0 then true
    else if negb (optr_eqb (m_next mr) (Some g)) then true
    else if negb (is_bouncing sc st) then true
    else if (9 * (m_last_idx mr + 1) <=? usage st sc) && (m_last_idx mr + 1 <? 20) then true else false.
Proof. reflexivity. Qed.

Ltac post_common MU WM MI ST FR MR m1 junk :=
  apply evt_done; exists m1, junk; split; [| exact (conj MU (conj WM (conj MI (conj ST (conj FR MR)))))].


End ENTRY.

