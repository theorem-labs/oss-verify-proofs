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
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast MallocTree MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_AB.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
Import ListNotations.
Open Scope Z_scope.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.


Ltac raw_store_finish A bs' FR ST MU WM SOK :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mX ?a ?bs) _) =>
    replace (write_to_mem mX a bs) with (write_to_mem mX (wa A) bs')
      by (f_equal; try reflexivity; try (rewrite le1_lit by lia; reflexivity); unfold wa, CTX; f_equal; lia);
    let L := fresh "LEN" in
    assert (L : Z.of_nat (length bs') = Z.of_nat (length bs')) by reflexivity;
    rewrite ?length_le8, ?length_le4, ?length_le2 in L at 1; cbn [length] in L;
    apply (rw_cells_frame asegs mX _ _ A bs') in FR; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [cells_size csize Nat.add]; lia];
    apply (stk_write asegs mX _ _ A bs') in ST; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia];
    apply (munch_write _ _ mX A bs') in MU; [| unfold CTX; lia | rewrite <- L; unfold CTX; lia | rewrite <- L; unfold CTX; cbn [inside]; lia];
    apply (wmono_write asegs _ mX (wa A) bs') in WM;
    lazymatch goal with HI : mem_inv asegs mX |- _ =>
      apply (mem_inv_store asegs mX (wa A) bs') in HI;
      [| first [ exact SOK | rewrite <- ?L; replace (wa A) with a by (unfold wa, CTX; f_equal; lia); exact SOK ] ]
    end;
    clear L SOK;
    let m' := fresh "m" in remember (write_to_mem mX (wa A) bs') as m' eqn:Em'; clear Em'
  end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_malloc_bigw () : Init.string Init.list := ["OSSVerify.KrLib.Heap.Malloc.upd_ctx"; "OSSVerify.KrLib.Heap.Malloc.set_mmap_counter"; "OSSVerify.KrLib.Heap.Malloc.put_meta"; "big_meta"; "OSSVerify.KrLib.Heap.Malloc.put_group"; "Corelib.Init.Datatypes.pair"; "Corelib.Numbers.BinNums.N"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.Some"; "OSSVerify.KrLib.Heap.Malloc.aptr"; "OSSVerify.KrLib.Heap.Malloc.hdr_havoc"; "big_metaA"; "OSSVerify.KrLib.Heap.Malloc.mstate"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "OSSVerify.KrLib.Heap.Malloc.shadow"; "stdpp.base.lookup"; "stdpp.gmap.gmap"; "stdpp.numbers.N.eq_dec"; "stdpp.countable.N_countable"; "stdpp.gmap.gmap_lookup"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.Malloc.s_shadow"; "Corelib.Init.Datatypes.None"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.ex"; "OSSVerify.KrLib.Heap.Malloc.cellval"; "OSSVerify.KrLib.Heap.Malloc.cell_read"; "OSSVerify.KrLib.Heap.Malloc.get_shadow"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.Unknown"].



Lemma unmap_seqs_empty st : unmap_seqs (upd_ctx (fun c => set_unmap_seq_map ∅ c) st) = zeros 32.
Proof. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import MallocKit_A2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require StrFun.

Definition big_ml (n : Z) : Z := Z.land ((n + IB + UNIT + 4095) / 4096) (2^52 - 1).
Definition big_meta (rid : N) (n : Z) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 1 63 (big_ml n).
Definition big_metaA (rid : N) : meta := mkMeta None None (Some (rid, 0)) 0 0 0 0 0 0.
(* [comment removed for export] *)
Definition big_st (st : mstate) (g : aptr) (rid : N) (n v : Z) : mstate := ltac2:(CDefT.buildp (gd_tbl_F_malloc_bigw ()) "(0.(1.O1.)(2.O4.(3.O3.O2.)(4.(5.$6.$7.O3.=)(8.$9.O4.)=(:.(5.$6.$7.O3.=)(2.O4.(;.O3.)O5.)))))")
(* [comment removed for export] *).

Lemma big_ml_eq n : 0 <= n < 2^32 -> big_ml n = (n + 4115) / 4096.
Proof.
  intros Hn. unfold big_ml, IB, UNIT. change (2^52 - 1) with (Z.ones 52). rewrite Z.land_ones by lia.
  replace (n + 4 + 16 + 4095) with (n + 4115) by lia. apply Z.mod_small. Z.div_mod_to_equations. lia.
Qed.


(* [comment removed for export] *)
Lemma cell_read_hdr_havoc_fresh : ltac2:(CDefT.buildp (gd_tbl_F_malloc_bigw ()) "Pst,$<.Pb,(=.$6.$7.)Po,$7.P,(>.(?.$10.)(11.$6.$10.(12.$6.$13.$14.$10.)(15.$6.$13.$14.$10.)(16.$6.$7.R2.)(17.R3.))(18.$10.))P,(>.$7.(19.(1:.$6.$7.R3.)+10.)=)P,(1;.(1<.=R3.)(1=.R3.+<.))(1>.$7.Lh,$7.(>.$1?.(20.(21.(:.R6.R7.)(16.$6.$7.R6.))(22.(1:.$6.$7.R6.)R5.))(23.R1.)))")
(* [comment removed for export] *).
Proof.
  intros st b o SH B16 Ho. unfold hdr_havoc, get_shadow, upd_shadow. cbn [s_shadow set_shadow].
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold get_shadow. rewrite SH. cbn [default from_option id r_cells r_hav r_havp shadow0].
  unfold cell_read. cbn [r_cells r_hav r_havp]. rewrite !lookup_empty.
  replace ((snd b + o) / 16) with (snd b / 16) by (Z.div_mod_to_equations; lia).
  rewrite lookup_insert_eq. cbn [default from_option id]. unfold hav_add. cbn.
  replace ((snd b + o) mod 16) with o by (Z.div_mod_to_equations; lia).
  replace (o <? 12) with true by (symmetry; apply Z.ltb_lt; lia). cbn. eexists. reflexivity.
Qed.


Lemma meta_word_big_range rid n : 0 <= n < 2^32 -> 0 <= meta_word (big_meta rid n) < 2^64.
Proof.
  intros Hn. unfold meta_word, big_meta. cbn [m_last_idx m_freeable m_sizeclass m_maplen]. rewrite big_ml_eq by lia.
  Z.div_mod_to_equations. lia.
Qed.


Lemma le4_sxv v : le4 (wz (sxv v)) = le4 (wz v).
Proof.
  apply le4_congr. rewrite wz_unsigned by apply sxv_range. rewrite sxv_mod32.
  unfold wz. rewrite Z_to_bv_unsigned. change (bv_modulus 64) with (2^64). symmetry. apply MallocRep.mod_mod_pow2. lia.
Qed.

Section SUCC.
Variables (st : mstate) (m : mem) (g : aptr) (rid : N) (x n c lo : Z).
Let G := conc st g.
Hypothesis MR : mrep st m.
Hypothesis TK : ticks_ok st.
Hypothesis G0 : get_meta_rec st g = meta0.
Hypothesis MSL : meta_slot st g.
Hypothesis RR : (s_regions st) !! rid = Some (mkRegion RKGroup x (n + IB + UNIT)).
Hypothesis GN : forall off, (s_groups st) !! (rid, off) = None.
Hypothesis AN : forall off, (s_areas st) !! (rid, off) = None.
Hypothesis SHN : (s_shadow st) !! rid = None.
Hypothesis HC : c_mmap_counter (ctx st) = c.
Hypothesis CR : 0 <= c < 2^32.
Hypothesis NR : MMAP_THRESHOLD <= n < 2^32.
Hypothesis CLO : s_ceil st <= lo.

End SUCC.


