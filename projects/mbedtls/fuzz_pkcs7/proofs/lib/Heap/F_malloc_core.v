(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp F_malloc_enf AllocSlot_iface Malloc_iface MallocHINV F_malloc_join F_malloc_small F_malloc_entry.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_malloc_core () : Init.string Init.list := ["OSSVerify.KrLib.Heap.MallocTree.mem"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.Heap.MallocBlocks.block"; "OSSVerify.KrLib.Heap.Prog.PState"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Numbers.BinNums.Z"; "Corelib.Numbers.BinNums.N"; "OSSVerify.KrLib.Heap.Malloc.set_tick"; "OSSVerify.KrLib.Heap.MallocBlocks.AREACH_from"; "OSSVerify.KrLib.Heap.MallocRep.agent_reserved"; "OSSVerify.KrLib.Heap.MallocFacts_A.MFACTS_g"; "OSSVerify.KrLib.Heap.MallocRep.mrep"; "Corelib.Init.Logic.eq"; "stdpp.bitvector.definitions.Z_to_bv"; "OSSVerify.KrLib.Heap.Malloc_iface.AGP"; "Stdlib.ZArith.BinInt.Z.le"; "OSSVerify.KrLib.Heap.Malloc.s_ceil"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Heap.MallocTree.AM_STACK"; "Corelib.Init.Logic.and"; "OSSVerify.KrLib.Heap.Malloc.MMAP_THRESHOLD"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "OSSVerify.KrLib.Heap.MallocTree.brk_link_ps"; "OSSVerify.KrLib.Heap.MallocRep.ticks_ok"; "OSSVerify.KrLib.Heap.Malloc_fp.unk_agree"; "OSSVerify.KrLib.Lib.Mem.mem_inv"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "OSSVerify.KrLib.Lib.Frame.stk"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Cells.C4"; "OSSVerify.KrLib.Heap.MallocTree.auxv_ok"; "OSSVerify.KrLib.Heap.MallocTree.pres_except"; "OSSVerify.KrLib.Heap.Malloc_fp.malloc_fp"; "OSSVerify.KrLib.Heap.MallocTree.implT"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.malloc_core"; "OSSVerify.KrLib.Heap.Malloc.full_lay"; "coreQ"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "OSSVerify.KrLib.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "Stdlib.NArith.BinNat.N.lt"; "OSSVerify.KrLib.Heap.Malloc.s_tick"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "OSSVerify.KrLib.Heap.Malloc.FUEL"].


(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition coreQ (o m0 : mem) (st : mstate) (s : PState)
    (ra sp gp tp s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0v : word) (F : bvmap 5 word) (fc : bv 32) (n lo : Z)
    (res : mstate * option (aptr * Z)) (s' : PState) (ms' : machine_state) : Prop :=
  match res with
  | (st2, Some (g, idx)) =>
    exists (b : aptr) (r : region) (m1 : mem) (junk : list byte) (errv : word) (t0 t1 t2 a0 a1 a3 a5 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR (Z_to_bv 64 0x17008) (Z_to_bv 64 (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz n) s1
                   a0 a1 (wz idx) a3 (wz (sxv (c_mmap_counter (ctx st2)))) a5 (pw st2 (Some g)) a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x17014) fc None m1 (seg_rom asegs)
      /\ mrep st2 m1 /\ ticks_ok st2 /\ unk_agree st2 o m1 /\ mem_inv asegs m1
      /\ stk asegs m1 lo (bv_unsigned sp + -64)
      /\ rw_cells asegs m1 (bv_unsigned sp + -64)
           [C8 (wz idx); C8 (pw st2 (Some g)); C8 (wz (sxv (c_mmap_counter (ctx st2)))); C8 (wz idx); CB 16 junk; C8 s0v; C8 ra]
      /\ rw_cells asegs m1 (errno_addr tp) [C4 errv] /\ auxv_ok m1 (bv_unsigned sp)
      /\ pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ (forall a, r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx - 4 <= a
                   < r_base r + snd b + 16 + get_stride (get_meta_rec st2 g) * idx + get_stride (get_meta_rec st2 g) - 4 ->
            malloc_fp st st2 lo (bv_unsigned sp) a)
      /\ 0 <= c_mmap_counter (ctx st2) < 2^32
      /\ slot_ok st2 g b r idx n
      /\ (expo_cond st n -> rdv pans_mem o st2 (fst b, snd b + (16 + get_stride (get_meta_rec st2 g) * idx) + -3) = 0)
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  | (st2, None) =>
    exists (m1 : mem) (errv : word) (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
      ms' = MS (mkR ra sp gp tp t0 t1 t2 s0v s1 (wz 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)
      /\ mrep st2 m1 /\ ticks_ok st2 /\ mem_inv asegs m1 /\ stk asegs m1 lo (bv_unsigned sp)
      /\ rw_cells asegs m1 (errno_addr tp) [C4 errv] /\ auxv_ok m1 (bv_unsigned sp)
      /\ pres_except (malloc_fp st st2 lo (bv_unsigned sp)) m0 m1
      /\ mrel st st2 /\ brk_link_ps st2 s' /\ ps_m s' = ps_m s /\ ps_fa s' = ps_fa s /\ ps_so s' = ps_so s
  end.


(* [comment removed for export] *)
Definition big_stmt : Prop := ltac2:(CDefT.buildp (gd_tbl_F_malloc_core ()) "Po,$0.Pm0,$0.Pst,$1.PLB,(2.$3.)Ps,$4.Pra,(5.&40.)Psp,(5.&40.)Pgp,(5.&40.)Ptp,(5.&40.)Ps1,(5.&40.)Ps2,(5.&40.)Ps3,(5.&40.)Ps4,(5.&40.)Ps5,(5.&40.)Ps6,(5.&40.)Ps7,(5.&40.)Ps8,(5.&40.)Ps9,(5.&40.)Ps10,(5.&40.)Ps11,(5.&40.)Ps0v,(5.&40.)PF,(6.&5.(5.&40.))Pfc,(5.&20.)Pn,$7.Plo,$7.Pt,$8.Pm1,$0.Pjunk,(2.(5.&8.))Perrv,(5.&40.)Pt0,(5.&40.)Pt1,(5.&40.)Pt2,(5.&40.)Pa1,(5.&40.)Pa2,(5.&40.)Pa3,(5.&40.)Pa4,(5.&40.)Pa6,(5.&40.)Pa7,(5.&40.)Pt3,(5.&40.)Pt4,(5.&40.)Pt5,(5.&40.)Pt6,(5.&40.)Pra',(5.&40.)Zst1,$1.(9.R12.R29.)P,(:.$;.R2:.R29.)P,(<.$;.R2;.R2:.)P,(=.R2<.R2=.)P,(>.(5.&40.)R28.(?.&40.$10.))P,(>.(5.&40.)R28.(?.&40.+1:620.))P,(11.(12.R2?.)R19.)P,(11.R1:.(13.(13.(14.&40.R2<.)+40.)$15.))P,(16.(11.$17.R1<.)(18.R1<.(19.+2.+20.)))P,(1:.R32.R30.)P,(=.R:.R1;.)P,(1;.R;.)P,(1<.R<.R37.R1=.)P,(1=.$1>.R1>.)P,(1?.$1>.R1?.R21.(20.(14.&40.R33.)-40.))P,(21.$1>.R20.(20.(14.&40.R34.)-40.)(22.$23.(24.#30.R1?.)(22.$23.(25.R26.)(22.$23.(25.R35.)(26.$23.)))))P,(>.$27.(28.(5.&8.)R20.)#30.)P,(21.$1>.R22.(20.(14.&40.R34.)-:4.)(22.$23.(29.R20.)(26.$23.)))P,(2:.R23.(14.&40.R37.))P,(2;.(2<.R3<.R13.R26.(14.&40.R38.))R3=.R24.)(2=.(2>.$1.(2?.(2>.$30.$7.)))R3?.(31.$32.R14.R28.)R3;.(33.R3?.R3>.R3=.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.)(34.(35.R15.(?.&40.(20.(14.&40.R39.)-40.))R38.R37.R22.R21.R20.(36.R28.)R36.(?.&40.R28.)R1?.R1>.R1=.R1<.(?.&40.+1??>;.)R1;.R1:.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R19.R18.R17.R16.)R2:.(?.&40.+16=60.)R29.(37.(5.&40.))R25.(38.$1>.)))")
(* [comment removed for export] *).

Section CORE.
Variables (as_pre : mstate -> mstate -> Z -> Z -> nat -> Prop) (as_inv : mstate -> mstate -> mstate -> Z -> Z -> Prop).
Hypothesis AS : alloc_slot_stmt as_pre as_inv.
Hypothesis AS_PRE : ltac2:(CDefT.buildp (gd_tbl_F_malloc_core ()) "Pst,$1.PLB,(2.$3.)Pt,$8.Psc,$7.Pn,$7.P,(:.$;.R5.R4.)P,(<.$;.R6.R5.)P,(39.(3:.R7.)R5.)P,(16.(11.=R5.)(18.R5.+30.))P,(16.(11.=R5.)(18.R5.(19.+2.+20.)))P,(11.(20.R6.+4.)(3;.+10.(3<.R7.)))A5.Vas_pre,R;.(9.R9.R;.)R8.R7.$3=.")
(* [comment removed for export] *).
Hypothesis BIG : big_stmt.

End CORE.

