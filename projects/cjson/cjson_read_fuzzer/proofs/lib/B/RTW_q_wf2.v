(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P Require Exit_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require BImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_leaves_memset.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_cid.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Ceil.
Module RTW_m_cidw.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_cid.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma cid_block_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (s : Z),
  mem_inv bsegs m -> a4 = wz s -> 513 <= s <= 65536 -> s mod 8 = 0 ->
  evt bsegs (fun ms' => exists (a2' a4' a5' a6' a7' t0' t1' : word),
                 ms' = MS (mkR ra sp gp tp t0' t1' t2 (wz (classid s)) s1 a0 a1 a2' a3 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (wz 0x36754) fc None m (seg_rom bsegs)
                 /\ munch [] m m /\ wmono bsegs m m /\ mem_inv bsegs m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz 0x36678) fc None m (seg_rom bsegs)).
Proof.
  intros until s. intros MI -> Hs Hm8.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  cbv beta delta [wz] in *.
  do 55 lstep.
  (* [comment removed for export] *)
  let v := reg_val 8 in
  lazymatch v with Z_to_bv 64 ?e => replace e with (classid s); [ | rewrite <- (cid_code_ok s) by lia; reflexivity ] end.
  finish.
Qed.


End CeilWrap.
End RTW_m_cidw.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_rep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_q_drainw.
Module RTW_m_c0.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_cid RTW_m_cidw OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Definition calloc_frame (ra s0 s1 s2 s3 s4 : word) : list cell := [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

Lemma calloc_c0p_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (n lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m ->
  a0 = wz A_ALLOC -> a1 = wz (acache st) -> a2 = wz (needed n) -> a3 = wz 8 ->
  0 <= n < 2^32 -> bprim n = true ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  evt bsegs (fun ms' => exists (a4' a5' a6' a7' t0' t1' : word) (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp + -48)) gp tp t0' t1' t2 (wz (pclass n)) (wz (pcaddr st (pclass n)))
                    (wz A_ALLOC) (wz (acache st)) (wz (zlen (cch st (pclass n)))) (wz 8) a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x36770) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells bsegs m' (bv_unsigned sp + -48) (calloc_frame ra s0 s1 s2 s3 s4))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x365c0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HR WF MI -> -> -> -> Hn HP ST CEIL LO.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (prim_facts n HP) as (PC & _).
  set (c := pclass n) in *.
  (* [comment removed for export] *)
  pose proof (proj1 (rr_cache st m HR c ltac:(unfold KNUMCLASSES; lia))) as CC.
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG in TR.
  assert (PCB : st_t st + 208 + 80 <= pcaddr st c /\ pcaddr st c + 80 <= st_t st + 2768) by (unfold pcaddr, acache, T_ACACHE; lia).
  assert (NDp : needed n = needed0 n) by (unfold needed; unfold bprim in HP; rewrite HP; reflexivity).
  pose proof (needed0_range n Hn) as NR. pose proof (rounded8_range n Hn) as R8. pose proof (rz_size_range n) as RZ.
  assert (N8 : needed0 n mod 8 = 0) by (unfold needed0; apply mod0_add; [lia| tauto | apply (mod0_trans _ 8 16); [lia|lia|reflexivity|tauto]]).
  assert (NP : needed0 n <= 65536) by (unfold bprim, is_primary, KMAXSIZE in HP; apply Z.leb_le in HP; exact HP).
  pose proof (wc_cache_max st c (wf_class_ok st WF c ltac:(unfold KNUMCLASSES; lia))) as CM. pose proof (cmaxcount_le16 c) as CM16.
  pose proof (zlen_nonneg (cch st c)) as CZ.
  rewrite NDp.
  unfold A_ALLOC in *. leaf_prep.
  carve_frame 48%nat ST.
  do 7 lstep.    (* [comment removed for export] *)
  lstep. lstep.  (* [comment removed for export] *)
  replace (needed0 n + Z.b2z (needed0 n <? 1)) with (needed0 n) by (destruct (Z.ltb_spec0 (needed0 n) 1); cbn; lia).
  lstep. try rewrite (Z.mod_small (needed0 n)) by lia. rewrite zb_lxor_ones by lia.  (* [comment removed for export] *)
  lstep; if_lia.  (* [comment removed for export] *)
  lstep. lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep; if2 BR.  (* [comment removed for export] *)
  - call cid_block_spec; [exact MI | reflexivity | lia | exact N8 | ]. cbv beta delta [wz].
    change (classid (needed0 n)) with c.
    lstep; if_lia. lstep. lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep. (* [comment removed for export] *)
    replace (acache st + c * 80) with (pcaddr st c) by (unfold pcaddr; lia).
    lstep. rewrite (sx32_lit (zlen (cch st c))) by lia.
    finish.
  - lstep. lstep. (* [comment removed for export] *)
    replace ((needed0 n + 31) ≫ 5) with c.
    2:{ subst c. unfold pclass, classid. destruct (Z.leb_spec0 (needed0 n) 512); [| exfalso; lia]. rewrite Z.shiftr_div_pow2 by lia. reflexivity. }
    lstep. (* [comment removed for export] *)
    lstep; if_lia. lstep. lstep; if_lia. (* [comment removed for export] *)
    lstep. lstep. lstep.
    replace (acache st + c * 80) with (pcaddr st c) by (unfold pcaddr; lia).
    lstep. rewrite (sx32_lit (zlen (cch st c))) by lia.
    finish.
Qed.

Lemma calloc_c0s_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (n lo : Z),
  mem_inv bsegs m ->
  a2 = wz (needed n) -> a3 = wz 8 ->
  0 <= n < 2^32 -> bprim n = false ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + 48 <= bv_unsigned sp ->
  evt bsegs (fun ms' => exists (m' : word -> option byte),
      ms' = MS (mkR ra (wz (bv_unsigned sp + -48)) gp tp t0 t1 t2 s0 s1 a0 a1 (wz (needed n)) (wz 8) (wz (needed n)) (wz 65536) a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (wz 0x36654) fc None m' (seg_rom bsegs)
      /\ munch [(lo, bv_unsigned sp)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + -48)
      /\ rw_cells bsegs m' (bv_unsigned sp + -48) (calloc_frame ra s0 s1 s2 s3 s4))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x365c0) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros MI -> -> Hn HP ST CEIL LO.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (sec_facts n HP) as (S1 & S2 & S3 & S4 & S5 & S6).
  pose proof (rounded8_range n Hn) as R8.
  assert (NR : 65536 < needed n < 2^33) by (rewrite S6; unfold bprim, is_primary, KMAXSIZE, needed0 in HP; apply Z.leb_gt in HP; lia).
  leaf_prep.
  carve_frame 48%nat ST.
  do 7 lstep.    (* [comment removed for export] *)
  lstep. lstep.  (* [comment removed for export] *)
  replace (needed n + Z.b2z (needed n <? 1)) with (needed n) by (destruct (Z.ltb_spec0 (needed n) 1); cbn; lia).
  lstep. try rewrite (Z.mod_small (needed n)) by lia. rewrite zb_lxor_ones by lia.  (* [comment removed for export] *)
  lstep; if_lia.  (* [comment removed for export] *)
  lstep. lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep. lstep; if_lia. (* [comment removed for export] *)
  lstep; if_lia. (* [comment removed for export] *)
  finish.
Qed.


End CeilWrap.
End RTW_m_c0.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_kit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_pop.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_bandtac4.
Module RTW_m_c1.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib RTW_m_c0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Lemma nthz_app_last : forall (pre : list Z) k, nthz (pre ++ [k]) (zlen pre) 0 = k.
Proof.
  intros pre k. unfold nthz, zlen. destruct (Z.ltb_spec0 (Z.of_nat (length pre)) 0); [lia|].
  rewrite Nat2Z.id. rewrite nth_middle with (l' := []) (d := 0) (a := k) (l := pre). reflexivity.
Qed.

(* [comment removed for export] *)
Lemma tstat_cell : forall st m, RTREP st m -> RTWF st -> exists v : word, rw_cells bsegs m (st_t st + 2784) [C8 v].
Proof.
  intros st m HR WF. pose proof (proj1 (rr_thread st m HR)) as V. pose proof (t_range st WF) as [T1 T2]. unfold KHIGHMEM_BEG, AIMG_HI in T1. olin_all.
  apply c8_of_bytes; [blia| lia|]. intros i Hi. destruct V as (_ & _ & V). apply V. lia.
Qed.

Lemma calloc_c1_spec :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (vra vs0 vs1 vs2 vs3 vs4 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (st : rtstate) (c k : Z) (pre : list Z) (lo : Z),
  RTREP st m -> RTWF st -> mem_inv bsegs m ->
  1 <= c <= 30 -> cch st c = pre ++ [k] ->
  a0 = wz A_ALLOC -> a1 = wz (acache st) -> a2 = wz (zlen pre + 1) -> a3 = wz 8 -> s0 = wz c -> s1 = wz (pcaddr st c) ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp -> bv_unsigned sp + 48 <= 2^64 ->
  rw_cells bsegs m (bv_unsigned sp) (calloc_frame vra vs0 vs1 vs2 vs3 vs4) ->
  evt bsegs (fun ms' => exists (a1' a2' a4' : word) (m' : word -> option byte),
      ms' = MS (mkR vra (wz (bv_unsigned sp + 48)) gp tp t0 t1 t2 vs0 vs1 (wz (cptr_addr st c k)) a1' a2' (wz 8) a4' a5 a6 a7
                    vs2 vs3 vs4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
               F (ret_pc vra) fc None m' (seg_rom bsegs)
      /\ munch [(pcaddr st c, pcaddr st c + 4); (st_t st + 2784, st_t st + 2792)] m m' /\ wmono bsegs m m' /\ mem_inv bsegs m'
      /\ stk bsegs m' lo (bv_unsigned sp + 48)
      /\ rw_cells bsegs m' (pcaddr st c) [W4 (zlen pre); W4 (pc_max_count st c); W8 (pc_class_size st c)])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz 0x36774) fc None m (seg_rom bsegs)).
Proof.
  intros until lo. intros HR WF MI Hc HC -> -> -> -> -> -> ST CEIL LO SPH FR.
  pose proof (munch_refl [(pcaddr st c, pcaddr st c + 4); (st_t st + 2784, st_t st + 2792)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
  destruct (rr_cache st m HR c HcK) as [CC CEN].
  assert (LEN : zlen (cch st c) = zlen pre + 1) by (rewrite HC, zlen_app, zlen_cons, zlen_nil; lia).
  rewrite LEN in CC.
  pose proof (zlen_nonneg pre) as PZ.
  pose proof (CEN (zlen pre) ltac:(lia)) as CE. rewrite HC, nthz_app_last in CE. clear CEN.
  pose proof (proj1 (rr_alloc st m HR)) as (j1 & j2 & j3 & AL).
  destruct (tstat_cell st m HR WF) as [sv SV].
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  pose proof (wb_t_align st (wf_base_ok st WF)) as TAL.
  assert (PCB : st_t st + 208 + 80 <= pcaddr st c /\ pcaddr st c + 80 <= st_t st + 2768) by (unfold pcaddr, acache, T_ACACHE; lia).
  pose proof (wc_cache_max st c (wf_class_ok st WF c HcK)) as CM. pose proof (cmaxcount_le16 c) as CM16. rewrite LEN in CM.
  (* [comment removed for export] *)
  assert (CV : carved_cptr st c k).
  { apply (wc_used_carved st c (wf_class_ok st WF c HcK)). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. right. rewrite HC. apply in_or_app. right. left. reflexivity. }
  destruct (carved_chunk st WF c k HcK ltac:(lia) CV) as (C1 & C2 & C3).
  pose proof (region_facts st WF c HcK) as RF. cbn zeta in RF. destruct RF as (X1 & X2 & X3 & X4 & X5 & X6 & X7 & X8 & X9 & X10).
  destruct CV as (j & Hj & Ek).
  assert (KB : 0 <= k < 2^28).
  { pose proof (chunk_cptr_eq c j ltac:(lia)) as E16. rewrite <- Ek in E16. unfold cptr_addr, KFREEARRAY_OFF in *.
    pose proof (csize_pos c ltac:(lia)). nia. }
  pose proof (S_range st WF) as (SR1 & SR2 & SR3). pose proof (P_range st WF) as (PR1 & PR2 & PR3).
  unfold KHIGHMEM_BEG, AIMG_HI, KSPACESIZE, PRIM_RES_SIZE, KREGIONSIZE, KFREEARRAY_OFF, KFREEARRAY_SIZE in *.
  unfold A_ALLOC in *. unfold calloc_frame in FR. leaf_prep.
  replace (pcaddr st c + 16 + 4 * zlen pre) with (pcaddr st c + 4 * zlen pre + 16) in CE by lia.
  lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) replace (acache st + 2576) with (st_t st + 2784) by (unfold acache, T_ACACHE; lia).
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  change 18446744073709551616 with (2^64). rewrite (shl32_shr30 (zlen pre)) by lia.
  lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *) rewrite (zx32_lit k) by lia.
  amo_zstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  lstep. lstep. lstep. lstep. (* [comment removed for export] *)
  lstep. lstep; if_lia. (* [comment removed for export] *)
  do 7 lstep. (* [comment removed for export] *)
  lstep. (* [comment removed for export] *)
  match goal with |- context [Z_to_bv 64 (?x + (?y + st_spacebeg st))] =>
    replace (x + (y + st_spacebeg st)) with (cptr_addr st c k)
      by (unfold cptr_addr; rewrite (rbeg_val st); unfold KREGIONSIZE; rewrite !Z.shiftl_mul_pow2 by lia; try rewrite unsigned_lit by lia; lia) end.
  release_frame FR ST (bv_unsigned sp + 48).
  finish.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition st_pop (st : rtstate) (c k : Z) (pre : list Z) : rtstate :=
  match st with
  | mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 a4 a5 (updz a6 c pre) a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 ((c, k) :: b1) b2 b3 b4 b5
  end.

Section POPM.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (a23 : list (Z * Z))
          (b1 b2 b3 : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Variables (c k : Z) (pre : list Z).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5.
Let st' := mkRT a1 a2 a3 a4 a5 (updz a6 c pre) a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 ((c, k) :: b1) b2 b3 b4 b5.
Hypothesis WF : RTWF st.
Hypothesis HX : tpx_ok st.
Hypothesis Hc : 1 <= c <= 30.
Hypothesis HC : cch st c = pre ++ [k].
Variables (m m' : word -> option byte).
Let W := [(pcaddr st c, pcaddr st c + 4); (st_t st + 2784, st_t st + 2792)].
Hypothesis MU : munch W m m'.
Hypothesis WM : wmono bsegs m m'.
Hypothesis HR : RTREP st m.
Hypothesis CC' : rw_cells bsegs m' (pcaddr st c) [W4 (zlen pre); W4 (pc_max_count st c); W8 (pc_class_size st c)].

Lemma pop_W_ok : Forall (tpz_ok st) W.
Proof.
  unfold W, tpz_ok. pose proof (t_range st WF). constructor; [| constructor; [| constructor]]; cbn [fst snd]; left;
    unfold pcaddr, acache, T_ACACHE, T_UNWINDING; lia.
Qed.

Lemma RTREP_pop : RTREP st' m'.
Proof.
  destruct (tpz_others st WF HX W pop_W_ok m m' MU WM HR) as (X1 & X2 & X3 & X4 & X5 & X6 & X8 & X9 & X10 & X11 & X12 & X13 & X14 & X15 & X16).
  pose proof (t_range st WF) as TR.
  assert (E1 : cch st' c = pre) by (apply cch_pop_same; assumption).
  assert (E2 : forall c', c' <> c -> cch st' c' = cch st c') by (intros; apply cch_pop_other; assumption).
  assert (E3 : apend_cptrs st' c = k :: apend_cptrs st c) by (apply apend_pop_same).
  assert (E4 : forall c', c' <> c -> apend_cptrs st' c' = apend_cptrs st c') by (intros; apply apend_pop_other; assumption).
  assert (PCB : forall d, pcaddr st d = st_t st + 208 + 80 * d) by (intros; reflexivity).
  Local Ltac dj PCB := cbn [disjoint_from cells_size Cells.csize Nat.add]; try change (Z.of_nat 4) with 4; try change (Z.of_nat 8) with 8; try change (Z.of_nat 16) with 16; rewrite !PCB; lia.
  constructor; try assumption.
  - (* [comment removed for export] *)
    intros c' k' Hc' Hin. apply (X6 c' k' Hc'). unfold avail_cptrs in *. change (rg st' c') with (rg st c') in Hin. change (cptr_addr st' c' k') with (cptr_addr st c' k').
    destruct (Z.eq_dec c' c) as [->|NE].
    + rewrite E1, E3 in Hin. rewrite HC. rewrite !in_app_iff in *. cbn [In] in *. tauto.
    + rewrite (E2 c' NE), (E4 c' NE) in Hin. exact Hin.
  - (* [comment removed for export] *)
    intros c' Hc'. pose proof (rr_cache st m HR c' Hc') as [OC OE].
    change (pcaddr st' c') with (pcaddr st c'). change (pc_max_count st' c') with (pc_max_count st c'). change (pc_class_size st' c') with (pc_class_size st c').
    destruct (Z.eq_dec c' c) as [->|NE].
    + rewrite E1. split; [exact CC'|]. intros i Hi. rewrite HC in OE.
      assert (L : zlen (pre ++ [k]) = zlen pre + 1) by (rewrite zlen_app, zlen_cons, zlen_nil; lia).
      specialize (OE i ltac:(rewrite L; lia)).
      replace (nthz (pre ++ [k]) i 0) with (nthz pre i 0) in OE.
      2:{ unfold nthz. destruct (Z.ltb_spec0 i 0); [reflexivity|]. rewrite app_nth1; [reflexivity|]. unfold zlen in Hi. lia. }
      pose proof (zlen_nonneg pre). pose proof (wc_cache_max st c (wf_class_ok st WF c Hc')) as CM. rewrite HC, L in CM. pose proof (cmaxcount_le16 c) as CM16. eapply (rwT W m m' MU WM); [exact OE|]. unfold W. dj PCB.
    + rewrite (E2 c' NE).
      pose proof (wc_cache_max st c' (wf_class_ok st WF c' Hc')) as CM. pose proof (cmaxcount_le16 c') as CM16. unfold KNUMCLASSES in Hc'.
      split.
      * eapply (rwT W m m' MU WM); [exact OC|]. unfold W. dj PCB.
      * intros i Hi. eapply (rwT W m m' MU WM); [exact (OE i Hi)|]. unfold W. dj PCB.
Qed.
End POPM.

(* [comment removed for export] *)
Lemma st_pop_unfold : forall st c k pre, st_pop st c k pre =
  match st with mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 b1 b2 b3 b4 b5 =>
    mkRT a1 a2 a3 a4 a5 (updz a6 c pre) a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 a23 ((c, k) :: b1) b2 b3 b4 b5 end.
Proof. reflexivity. Qed.

Lemma RTWF_pop' : forall st c k pre, RTWF st -> 1 <= c <= 30 -> cch st c = pre ++ [k] -> st_apend st = [] -> RTWF (st_pop st c k pre).
Proof. intros st c k pre WF Hc HC HAP. destruct st. eapply RTWF_pop; eauto. Qed.
Lemma rt_prov_pop' : forall st c k pre, RTWF st -> 1 <= c <= 30 -> cch st c = pre ++ [k] -> st_apend st = [] -> rt_prov (st_pop st c k pre) <= rt_prov st + 2 * csize c.
Proof. intros st c k pre WF Hc HC HAP. destruct st. eapply rt_prov_pop; eauto. Qed.
Lemma RTMODEL_pop' : forall st c k pre mo, RTMODEL st mo -> RTMODEL (st_pop st c k pre) mo.
Proof. intros st c k pre mo H. destruct st. exact H. Qed.
Lemma SWIN_pop' : forall st c k pre g, SWIN st g -> SWIN (st_pop st c k pre) g.
Proof. intros st c k pre g H. destruct st. exact H. Qed.
Lemma GWIN_pop' : forall st c k pre m mo g, GWIN st m mo g -> GWIN (st_pop st c k pre) m mo g.
Proof. intros st c k pre m mo g H. destruct st. exact H. Qed.
Lemma RTREP_pop' : forall st c k pre m m',
  RTWF st -> tpx_ok st -> 1 <= c <= 30 -> cch st c = pre ++ [k] ->
  munch [(pcaddr st c, pcaddr st c + 4); (st_t st + 2784, st_t st + 2792)] m m' -> wmono bsegs m m' -> RTREP st m ->
  rw_cells bsegs m' (pcaddr st c) [W4 (zlen pre); W4 (pc_max_count st c); W8 (pc_class_size st c)] ->
  RTREP (st_pop st c k pre) m'.
Proof. intros st c k pre m m' WF HX Hc HC MU WM HR CC'. destruct st. eapply RTREP_pop; eauto. Qed.
(* [comment removed for export] *)
Lemma st_pop_same : forall st c k pre,
  st_sp0 (st_pop st c k pre) = st_sp0 st /\ st_lb (st_pop st c k pre) = st_lb st /\ st_lf (st_pop st c k pre) = st_lf st
  /\ st_trs (st_pop st c k pre) = st_trs st /\ st_apend (st_pop st c k pre) = (c, k) :: st_apend st
  /\ st_spend (st_pop st c k pre) = st_spend st /\ st_sec (st_pop st c k pre) = st_sec st
  /\ st_qpend (st_pop st c k pre) = st_qpend st /\ st_qtmp (st_pop st c k pre) = st_qtmp st /\ st_qcur (st_pop st c k pre) = st_qcur st
  /\ st_qthread (st_pop st c k pre) = st_qthread st /\ st_qglobal (st_pop st c k pre) = st_qglobal st /\ st_depot (st_pop st c k pre) = st_depot st
  /\ st_fs (st_pop st c k pre) = st_fs st /\ st_t (st_pop st c k pre) = st_t st /\ st_spacebeg (st_pop st c k pre) = st_spacebeg st
  /\ st_pbase (st_pop st c k pre) = st_pbase st /\ st_pa (st_pop st c k pre) = st_pa st
  /\ st_ctx (st_pop st c k pre) = st_ctx st /\ st_tls (st_pop st c k pre) = st_tls st /\ st_cache_inited (st_pop st c k pre) = st_cache_inited st
  /\ st_regions (st_pop st c k pre) = st_regions st /\ st_nreserved (st_pop st c k pre) = st_nreserved st
  /\ st_trs0 (st_pop st c k pre) = st_trs0 st /\ st_hints (st_pop st c k pre) = st_hints st /\ st_loose0 (st_pop st c k pre) = st_loose0 st
  /\ st_ia_inited (st_pop st c k pre) = st_ia_inited st /\ st_cache (st_pop st c k pre) = updz (st_cache st) c pre.
Proof. intros st c k pre. destruct st. cbn. repeat (split; [reflexivity|]). reflexivity. Qed.


End CeilWrap.
End RTW_m_c1.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require PropExec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require MState.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Step.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Frame.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Exec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Spin.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require SRealizes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_m_specs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
Module RTW_m_calloc.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.MState OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Step OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Frame OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Exec OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.Spin OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.SRealizes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.P.Exit_tac.STRW_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_malloc_leaves_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_tac.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_leaves_memset.RTW_leaves_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_q_drainw.RTW_m_a1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_m_lib OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_tpz RTW_m_c0 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_specs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_bandtac2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_bandtac4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CALLOC.
Hypothesis refill_proof : refill_spec.
Hypothesis large_alloc_proof : large_alloc_specW.   (* [comment removed for export] *)

Lemma zlen_pos_split : forall (l : list Z), 0 < zlen l -> exists pre k, l = pre ++ [k].
Proof.
  intros l H. destruct l as [|x l']; [cbn in H; unfold zlen in H; cbn in H; lia|].
  destruct (exists_last (l := x :: l') ltac:(discriminate)) as (pre & k & E). exists pre, k. exact E. (* [comment removed for export] *)
Qed.

Lemma nrefill_pos : forall c, 1 <= nrefill c <= 8.
Proof. intros c. unfold nrefill, cmaxcount, clampz. rewrite (Z.mul_comm 2), Z.div_mul by lia. lia. Qed.

(* [comment removed for export] *)
Lemma calloc_rel_pop : forall st n k pre, bprim n = true ->
  calloc_rel st (st_pop st (pclass n) k pre) n (cptr_addr st (pclass n) k).
Proof.
  intros st n k pre HP. pose proof (st_pop_same st (pclass n) k pre) as E.
  destruct E as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28). (* [comment removed for export] *)
  unfold calloc_rel, same_client. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]). right. left. split; [exact HP|]. exists k. auto.
Qed.

Lemma calloc_rel_refill_pop : forall st st1 n k pre, bprim n = true -> refill_rel st st1 (pclass n) 1 ->
  calloc_rel st (st_pop st1 (pclass n) k pre) n (cptr_addr st (pclass n) k).
Proof.
  intros st st1 n k pre HP nelH_; (nelim nelH_ 5%nat; intros SBP AP _ _ _). pose proof (st_pop_same st1 (pclass n) k pre) as E.
  destruct E as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & E27 & E28). (* [comment removed for export] *)
  destruct SBP as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24). (* [comment removed for export] *)
  unfold calloc_rel, same_client. rewrite E1, E2, E3, E4, E5, E6, E7, E8, E9, E10, E11, E12, E13, E14, E15, E16, E17, E18.
  rewrite P1, P3, P2, P4, P6, P7, P8, P9, P10, P12, P14, P15, P20, P21, P22, P23, P24, AP.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]). right. left. split; [exact HP|]. exists k. auto.
Qed.

Lemma calloc_rel_refill0 : forall st st1 n, refill_rel st st1 (pclass n) 0 -> calloc_rel st st1 n 0.
Proof.
  intros st st1 n nelH_; (nelim nelH_ 5%nat; intros SBP AP _ _ _).
  (nelim SBP 24%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24).
  unfold calloc_rel, same_client.
  rewrite P1, P3, P2, P4, P6, P7, P8, P9, P10, P12, P14, P15, P20, P21, P22, P23, P24, AP.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]). left. auto.
Qed.

Lemma calloc_rel_sec : forall st st1 n r, bprim n = false -> sec_alloc_rel st st1 n r -> calloc_rel st st1 n r.
Proof.
  intros st st1 n r HP nelH_; (nelim nelH_ 3%nat; intros SBS QC RES).
  (nelim SBS 24%nat; intros P1 P2 P3 P4 P5 P6 P7 P8 P9 P10 P11 P12 P13 P14 P15 P16 P17 P18 P19 P20 P21 P22 P23 P24).
  unfold calloc_rel, same_client.
  rewrite P1, P3, P2, P7, P8, P9, P10, P11, P13, P15, P16, P21, P22, P23, P24, QC.
  split; [repeat split; reflexivity|]. repeat (split; [reflexivity|]).
  destruct RES as [(-> & S1 & S2 & S3)|(mb & -> & M1 & M2 & M3 & S1 & S2 & S3)].
  - left. auto.
  - right. right. split; [exact HP|]. exists mb. repeat (split; [first [reflexivity| assumption]|]). exact P6.
Qed.

Theorem combined_alloc_proof : combined_alloc_spec.
Proof.
  unfold combined_alloc_spec. intros until lo. intros (HR & WF & HM & HG & HFR & HSWR) HTPX HAP0 Hn -> -> -> -> TP HDEP ST HCL LO SPS MI.
  pose proof (wb_sp0 st (wf_base_ok st WF)) as SP0. unfold ACALLOC_STACK, AREFILL_STACK in LO.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. idtac.
  apply lscps_assume. intros NWX HO HB.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl bsegs m) as WM.
  pose proof (t_range st WF) as TR. unfold KHIGHMEM_BEG, AIMG_HI in TR. olin_all.
  destruct (bprim n) eqn:HP.
  - (* [comment removed for export] *)
    pose proof (prim_facts n HP) as (PC & _). set (c := pclass n) in *.
    assert (HcK : 0 <= c < KNUMCLASSES) by (unfold KNUMCLASSES; lia).
    assert (DEP : calloc_deposit n = 2 * csize c) by (unfold calloc_deposit; rewrite HP; reflexivity). rewrite DEP in HDEP.
    pose proof (csize_pos c ltac:(lia)) as CSP.
    eapply lscps_step_evt.
    callx ltac:(eapply calloc_c0p_spec with (lo := lo) (st := st) (n := n);
                [exact HR| exact WF| exact MI| reflexivity| reflexivity| reflexivity| reflexivity| exact Hn| exact HP| exact ST| idtac; lia| lia]).
    fold c. cbv beta delta [wz]. rename PC0 into ST. rename POST into FR. rename MI0 into MI.
    rtrep_high HR WF MU WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (CP0 : cli_pres st (bv_unsigned sp) m mA).
    { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
    assert (HG0 : GWIN st mA mo g) by (eapply GWIN_mem; eauto).
    assert (ES0 : errno_same m mA).
    { eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. left. unfold AERRNO, ATP. lia. }
    clear MU WM.
    pose proof (zlen_nonneg (cch st c)) as CZ.
    destruct (Z.eq_dec (zlen (cch st c)) 0) as [Z0|NZ].
    + (* [comment removed for export] *)
      assert (EC : cch st c = []) by (destruct (cch st c) as [|x' l']; [reflexivity| rewrite zlen_cons in Z0; pose proof (zlen_nonneg l'); lia]).
      rewrite Z0. lstep; if_lia.
      do 7 lstep. lstep. (* [comment removed for export] *)
      apply evt_done.
      eapply lscps_bind.
      { pose proof refill_proof as RP. unfold refill_spec in RP. eapply RP with (lo := lo) (cls := c); try reflexivity.
        - exact (RTS_intro _ _ _ _ HR WF HM HG0 HFR HSWR).
        - lia. - exact EC. - exact TP. - lia.
        - rewrite unsigned_lit by lia. exact ST. - idtac; lia. - rewrite unsigned_lit by lia. unfold AREFILL_STACK. lia. - exact MI. }
      cbv beta. intros ms1 mo1 g1 PO.
      (nelim PO 28%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 st1 -> MI1 r -> RR RTS1 ST1 CP1 RF1 GM1 BO1).
      rewrite unsigned_lit in ST1, CP1 by lia.
      replace (ret_pc (Z_to_bv 64 0x36870)) with (Z_to_bv 64 0x36870) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in FR; [| left; cbn; lia].
      (nelim RTS1 6%nat; intros HR1 WF1 HM1 HG1 HF1 HSW1).
      pose proof RR as RR0. (nelim RR 5%nat; intros SBP AP1 CI1 OTH RES).
      assert (Et : st_t st1 = st_t st) by ((nelim SBP 16%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ _ E _); exact E).
      assert (Esp0 : st_sp0 st1 = st_sp0 st) by (destruct SBP as (E & _); exact E).
      assert (Esb : st_spacebeg st1 = st_spacebeg st) by ((nelim SBP 4%nat; intros _ _ E _); exact E).
      assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
      { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|]. eapply cj_pres_weaken; [exact CP1| lia| auto| auto]. }
      clear ST MI CP0 CP1.
      apply lscps_assume. intros _ HO1 HB1.
      destruct RES as [[-> LEN1]|[-> EC1]].
      * (* [comment removed for export] *)
        pose proof (nrefill_pos c) as NP1.
        (nelim (zlen_pos_split (cch st1 c) ltac:(lia)) 3%nat; intros pre k EC1).
        assert (LENp : zlen pre + 1 = nrefill c) by (rewrite <- LEN1, EC1, zlen_app, zlen_cons, zlen_nil; lia).
        pose proof (proj1 (rr_cache st1 m1 HR1 c HcK)) as CC1.
        replace (pcaddr st1 c) with (pcaddr st c) in CC1 by (unfold pcaddr, acache; rewrite Et; reflexivity). rewrite LEN1 in CC1.
        pose proof (munch_refl [(pcaddr st1 c, pcaddr st1 c + 4); (st_t st1 + 2784, st_t st1 + 2792)] m1) as MU2. pose proof (wmono_refl bsegs m1) as WM2.
        eapply lscps_step_evt. cbv beta delta [wz] in *.
        lstep; if_lia. (* [comment removed for export] *)
        lstep. rewrite (sx32_lit (nrefill c)) by lia. (* [comment removed for export] *)
        lstep. lstep. lstep. lstep. (* [comment removed for export] *)
        rewrite <- LENp.
        callx ltac:(eapply calloc_c1_spec with (lo := lo) (st := st1) (c := c) (k := k) (pre := pre) (vra := ra) (vs0 := s0) (vs1 := s1) (vs2 := s2) (vs3 := s3) (vs4 := s4);
          [ exact HR1| exact WF1| exact MI1| lia| exact EC1| reflexivity| unfold acache; rewrite Et; reflexivity| reflexivity| reflexivity| reflexivity
          | unfold pcaddr, acache; rewrite Et; reflexivity
          | rewrite unsigned_lit by lia; exact ST1| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
          | rewrite unsigned_lit by lia; exact FR ]).
        rewrite unsigned_lit in * by lia. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end. rename MI into MI2.
        apply evt_done. apply lscps_done.
        unfold calloc_post, rt_post_std. nexists 15%nat. exists m2, (st_pop st1 c k pre). split; [reflexivity|]. split; [exact MI2|].
        exists (cptr_addr st c k).
        (* [comment removed for export] *)
        assert (CV : carved_cptr st1 c k).
        { apply (wc_used_carved st1 c (wf_class_ok st1 WF1 c HcK)). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. right. rewrite EC1. apply in_or_app. right. left. reflexivity. }
        (nelim (carved_chunk st1 WF1 c k HcK ltac:(lia) CV) 3%nat; intros C1 C2 C3).
        pose proof (region_facts st1 WF1 c HcK) as RF. cbn zeta in RF. (nelim RF 7%nat; intros X1 X2 X3 X4 X5 X6 _).
        assert (ECP : cptr_addr st1 c k = cptr_addr st c k) by (unfold cptr_addr, rbeg; rewrite Esb; reflexivity).
        unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, PRIM_RES_SIZE, KFREEARRAY_OFF in X1, X3, X4, X6.
        split; [rewrite ECP; reflexivity|]. split; [rewrite <- ECP; lia|].
        split; [apply calloc_rel_refill_pop; [exact HP| exact RR0]|].
        split.
        { apply RTS_intro.
          - eapply RTREP_pop'; [exact WF1| apply HTPX; exact WF1| lia| exact EC1| exact MU2| exact WM2| exact HR1| exact POST].
          - apply RTWF_pop'; [exact WF1| lia| exact EC1| rewrite AP1; exact HAP0].
          - apply RTMODEL_pop'. exact HM1.
          - apply GWIN_pop'. eapply GWIN_mem; [exact HG1| exact HO1| exact WM2].
          - exact HF1.
          - apply SWIN_pop'. exact HSW1. }
        split; [assumption|].
        split.
        { unfold cli_pres in *. eapply cj_pres_trans; [exact CP01|].
          eapply (cli_pres_tpz st1 WF1 (bv_unsigned sp) ltac:(unfold CEIL; lia)) in MU2; [| exact WM2|].
          - unfold cli_pres in MU2. rewrite Esp0 in MU2. (nelim SBP 21%nat; intros _ _ _ _ _ _ _ _ _ _ _ _ _ P14 _ _ _ _ _ P20 _). rewrite P14, P20 in MU2. exact MU2.
          - constructor; [| constructor; [| constructor]]; cbn [fst snd]; left; unfold pcaddr, acache, T_ACACHE; lia. }
        split.
        { eapply errno_same_trans; [exact ES0|]. eapply errno_same_trans.
          - eapply errno_same_rt_frame; [exact RF1| unfold AERRNO, ATP; lia| intros a Ha; apply notin_ivs_app; [apply (errno_notin_primary_fp st c a WF HcK Ha)| apply (errno_notin_fp_emb st1 a WF1 Ha)]]   (* [comment removed for export] *).
          - eapply errno_same_munch; [exact MU2|]. pose proof (t_range st1 WF1) as TRx. olin TRx.
            constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold pcaddr, acache, T_ACACHE, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI in *; lia. }
        split; [exact GM1|].
        split.
        { replace (cptr_addr st c k =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite <- ECP; lia).
          pose proof (rt_prov_pop' st1 c k pre WF1 ltac:(lia) EC1 ltac:(rewrite AP1; exact HAP0)). rewrite DEP. unfold budget_ok in *. lia. }
        intros HF. rewrite HP in HF. discriminate.
      * (* [comment removed for export] *)
        eapply lscps_step_evt. cbv beta delta [wz] in *. unfold calloc_frame in FR.
        lstep; if_lia. (* [comment removed for export] *)
        lstep. lstep. lstep; if_lia. (* [comment removed for export] *)
        lstep. (* [comment removed for export] *)
        do 7 lstep. lstep. (* [comment removed for export] *)
        rewrite unsigned_lit in * by lia. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
        release_frame FR ST1 (bv_unsigned sp).
        apply evt_done. apply lscps_done.
        unfold calloc_post, rt_post_std. nexists 15%nat. exists m1, st1. split; [reflexivity|]. split; [exact MI1|].
        exists 0. split; [reflexivity|]. split; [lia|]. split; [apply calloc_rel_refill0; exact RR0|].
        split; [exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HF1 HSW1)|].
        split; [exact ST1|]. split; [exact CP01|].
        split.
        { eapply errno_same_trans; [exact ES0|].
          eapply errno_same_rt_frame; [exact RF1| unfold AERRNO, ATP; lia| intros a Ha; apply notin_ivs_app; [apply (errno_notin_primary_fp st c a WF HcK Ha)| apply (errno_notin_fp_emb st1 a WF1 Ha)]]   (* [comment removed for export] *). }
        split; [exact GM1|]. split; [cbn [Z.eqb]; exact BO1|].
        intros HF. rewrite HP in HF. discriminate.
    + (* [comment removed for export] *)
      (nelim (zlen_pos_split (cch st c) ltac:(lia)) 3%nat; intros pre k EC).
      assert (LENp : zlen (cch st c) = zlen pre + 1) by (rewrite EC, zlen_app, zlen_cons, zlen_nil; lia).
      pose proof (munch_refl [(pcaddr st c, pcaddr st c + 4); (st_t st + 2784, st_t st + 2792)] mA) as MU2. pose proof (wmono_refl bsegs mA) as WM2.
      pose proof (zlen_nonneg pre). pose proof (wc_cache_max st c (wf_class_ok st WF c HcK)) as CM. pose proof (cmaxcount_le16 c) as CM16. rewrite LENp in CM.
      rewrite LENp. lstep; if_lia. (* [comment removed for export] *)
      callx ltac:(eapply calloc_c1_spec with (lo := lo) (st := st) (c := c) (k := k) (pre := pre) (vra := ra) (vs0 := s0) (vs1 := s1) (vs2 := s2) (vs3 := s3) (vs4 := s4);
        [ exact HR| exact WF| exact MI| lia| exact EC| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity
        | rewrite unsigned_lit by lia; exact ST| idtac; lia| rewrite unsigned_lit by lia; lia| rewrite unsigned_lit by lia; lia
        | rewrite unsigned_lit by lia; exact FR ]).
      rewrite unsigned_lit in * by lia. replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end. rename MI0 into MI2.
      apply evt_done. apply lscps_done.
      unfold calloc_post, rt_post_std. nexists 15%nat. exists m2, (st_pop st c k pre). split; [reflexivity|]. split; [exact MI2|].
      exists (cptr_addr st c k).
      assert (CV : carved_cptr st c k).
      { apply (wc_used_carved st c (wf_class_ok st WF c HcK)). unfold used_cptrs, avail_cptrs. rewrite !in_app_iff. left. right. rewrite EC. apply in_or_app. right. left. reflexivity. }
      (nelim (carved_chunk st WF c k HcK ltac:(lia) CV) 3%nat; intros C1 C2 C3).
      pose proof (region_facts st WF c HcK) as RF. cbn zeta in RF. (nelim RF 7%nat; intros X1 X2 X3 X4 X5 X6 _).
      unfold KHIGHMEM_BEG, AIMG_HI, KREGIONSIZE, PRIM_RES_SIZE, KFREEARRAY_OFF in X1, X3, X4, X6.
      split; [reflexivity|]. split; [lia|].
      split; [apply calloc_rel_pop; exact HP|].
      split.
      { apply RTS_intro.
        - eapply RTREP_pop'; [exact WF| apply HTPX; exact WF| lia| exact EC| exact MU2| exact WM2| exact HR| exact POST].
        - apply RTWF_pop'; [exact WF| lia| exact EC| exact HAP0].
        - apply RTMODEL_pop'. exact HM.
        - apply GWIN_pop'. eapply GWIN_mem; [exact HG0| exact HO| exact WM2].
        - exact HFR.
        - apply SWIN_pop'. exact HSWR. }
      split; [assumption|].
      split.
      { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|].
        eapply (cli_pres_tpz st WF (bv_unsigned sp) ltac:(unfold CEIL; lia)) in MU2; [| exact WM2|].
        - exact MU2.
        - constructor; [| constructor; [| constructor]]; cbn [fst snd]; left; unfold pcaddr, acache, T_ACACHE; lia. }
      split.
      { eapply errno_same_trans; [exact ES0|]. eapply errno_same_munch; [exact MU2|]. pose proof (t_range st WF) as TRx. olin TRx.
        constructor; [| constructor; [| constructor]]; cbn [fst snd]; unfold pcaddr, acache, T_ACACHE, AERRNO, ATP, KHIGHMEM_BEG, AIMG_HI in *; lia. }
      split; [intros w Hw; exact Hw|].
      split.
      { replace (cptr_addr st c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia).
        pose proof (rt_prov_pop' st c k pre WF ltac:(lia) EC HAP0). rewrite DEP. unfold budget_ok in *. lia. }
      intros HF. rewrite HP in HF. discriminate.
  - (* [comment removed for export] *)
    (nelimp (sec_facts n HP) 6%nat; intros S1 S2 S3 S4 S5 S6). pose proof (rounded8_range n Hn) as R8. unfold usz in S4.
    assert (DEP : calloc_deposit n = SEC_ALLOC_COST n + SEC_SLOT_TAX) by (unfold calloc_deposit; rewrite HP; reflexivity). rewrite DEP in HDEP.
    eapply lscps_step_evt.
    callx ltac:(eapply calloc_c0s_spec with (lo := lo) (n := n);
                [exact MI| reflexivity| reflexivity| exact Hn| exact HP| exact ST| idtac; lia| lia]).
    cbv beta delta [wz].
    match goal with H : stk _ _ lo _ |- _ => rename H into ST end.
    match goal with H : rw_cells _ _ _ (calloc_frame _ _ _ _ _ _) |- _ => rename H into FR end.
    match goal with H : mem_inv _ _ |- _ => rename H into MI end.
    rtrep_high HR WF MU WM.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mA end.
    assert (CP0 : cli_pres st (bv_unsigned sp) m mA).
    { eapply (cli_pres_tpz st WF); [| exact MU| exact WM|]; [unfold CEIL; lia|]. constructor; [| constructor]. cbn [fst snd]. right. unfold CEIL. lia. }
    assert (HG0 : GWIN st mA mo g) by (eapply GWIN_mem; eauto).
    assert (ES0 : errno_same m mA).
    { eapply errno_same_munch; [exact MU|]. constructor; [| constructor]. cbn [fst snd]. left. unfold AERRNO, ATP. lia. }
    clear MU WM.
    unfold A_ALLOC. lstep. lstep. lstep. lstep. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    apply evt_done.
    eapply lscps_bind.
    { pose proof large_alloc_proof as LP. unfold large_alloc_specW in LP. eapply LP with (lo := lo) (n := n); try reflexivity.
      - exact (RTS_intro _ _ _ _ HR WF HM HG0 HFR HSWR).
      - lia. - exact HP. - rewrite S6. lia. - exact TP. - lia.
      - rewrite unsigned_lit by lia. exact ST. - idtac; lia. - rewrite unsigned_lit by lia. unfold ALARGE_ALLOC_STACK. lia. - exact MI. }
    cbv beta. intros ms1 mo1 g1 PO.
    (nelim PO 28%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m1 st1 -> MI1 r -> SR RTS1 ST1 CP1 R0 RS GM1).
    rewrite unsigned_lit in ST1, CP1, R0, RS by lia.
    replace (ret_pc (Z_to_bv 64 0x36668)) with (Z_to_bv 64 0x36668) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply (cj_pres_rw_cells _ _ _ _ _ _ _ _ CP1) in FR; [| left; cbn; lia].
    (nelim RTS1 6%nat; intros HR1 WF1 HM1 HG1 HF1 HSW1).
    assert (CP01 : cli_pres st (bv_unsigned sp) m m1).
    { unfold cli_pres in *. eapply cj_pres_trans; [exact CP0|]. eapply cj_pres_weaken; [exact CP1| lia| auto| auto]. }
    clear ST MI CP0 CP1.
    eapply lscps_step_evt. cbv beta delta [wz] in *. unfold calloc_frame in FR.
    lstep. lstep. lstep; if_lia. (* [comment removed for export] *)
    lstep. (* [comment removed for export] *)
    do 7 lstep. lstep. (* [comment removed for export] *)
    try rewrite unsigned_lit in * by lia. try replace (bv_unsigned sp + -48 + 48) with (bv_unsigned sp) in * by lia. try rewrite Z_to_bv_bv_unsigned.
    release_frame FR ST1 (bv_unsigned sp).
    apply evt_done. apply lscps_done.
    unfold calloc_post, rt_post_std. nexists 15%nat. exists m1, st1. split; [reflexivity|]. split; [exact MI1|].
    exists r.
    (nelimp SR 3%nat; intros _ _ RES).
    split; [reflexivity|].
    split.
    { destruct RES as [(-> & _)|(mb & -> & M1 & M2 & M3 & _)]; [lia|]. unfold sec_alloc_beg, SEC_HDR, KHIGHMEM_BEG, AIMG_HI in *. idtac. blia. }
    split; [apply calloc_rel_sec; [exact HP| exact SR]|].
    split; [exact (RTS_intro _ _ _ _ HR1 WF1 HM1 HG1 HF1 HSW1)|].
    split; [exact ST1|]. split; [exact CP01|].
    split.
    { eapply errno_same_trans; [exact ES0|]. destruct RES as [(-> & _)|(mb & -> & M1 & M2 & M3 & _)].
      - eapply errno_same_rt_frame; [exact (proj1 (R0 eq_refl))| unfold AERRNO, ATP; lia|].
        intros a Ha. apply (errno_notin_secondary_fp0 st a WF Ha).
      - eapply errno_same_rt_frame; [exact (proj1 (RS mb eq_refl M1))| unfold AERRNO, ATP; lia|].
        intros a Ha. apply (errno_notin_secondary_fp st mb n a WF M1 Ha). }
    split; [exact GM1|].
    split.
    { destruct RES as [(-> & _)|(mb & -> & M1 & M2 & M3 & _)].
      - cbn [Z.eqb]. apply R0. reflexivity.
      - replace (sec_alloc_beg mb =? 0) with false by (symmetry; apply Z.eqb_neq; pose proof (ablk_img _ _ M1); unfold sec_alloc_beg, SEC_HDR, KHIGHMEM_BEG, AIMG_HI in *; lia).
        rewrite DEP. apply (RS mb eq_refl M1). }
    intros _ mb Hr Hmb. (nelim (RS mb Hr Hmb) 5%nat; intros _ _ P1 P2 P3). split; [exact P1| split; [exact P2| exact P3]].
Qed.
End CALLOC.


End CeilWrap.
End RTW_m_calloc.

(* [comment removed for export] *)
From Stdlib Require Permutation.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Module RTW_q_wf.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.BImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_rep OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop.RT_artP OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_artF OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_m_pop RTW_m_c1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition QREC_MAX : Z := 2 * QUAR_MAX_SIZE + QUAR_MAX_CACHE + QBATCH_SIZE.
Definition wf_quarq (st : rtstate) : Prop :=
  (forall b, In b (qall st) -> qb_count b <= QBATCH_CAP /\ exists k, carved_cptr st 24 k /\ qb_addr b = cptr_addr st 24 k)
  /\ (forall b, In b (st_qthread st) -> 1 <= qb_count b)
  /\ qc_bytes (st_qglobal st) + qc_bytes (st_qtmp st) + qc_bytes (map fst (st_qcur st)) <= QREC_MAX
  /\ (zlen (st_apend st) <= 1 /\ zlen (st_qpend st) <= 1)
  /\ (forall bd, In bd (st_qcur st) -> 0 <= snd bd <= qb_count (fst bd))
  /\ (forall ck, In ck (st_apend st) -> 1 <= fst ck < KNUMCLASSES).
Definition RTWFq (st : rtstate) : Prop :=
  wf_base st /\ (forall c, 0 <= c < KNUMCLASSES -> wf_class st c) /\ wf_blocks st /\ wf_sec st /\ wf_quarq st
  /\ wf_depot st /\ wf_fs st.

Lemma RTWFq_of : forall st, RTWF st -> RTWFq st.
Proof.
  intros st WF. pose proof (wf_quar_ok st WF) as WQ.
  split; [exact (wf_base_ok st WF)|]. split; [exact (wf_class_ok st WF)|]. split; [exact (wf_blocks_ok st WF)|].
  split; [exact (wf_sec_ok st WF)|]. split; [| split; [exact (wf_depot_ok st WF)| exact (wf_fs_ok st WF)]].
  split; [exact (wq_batch st WQ)|]. split; [exact (wq_thread_nonempty st WQ)|]. split; [exact (wq_rec_max st WQ)|].
  split; [exact (wq_inflight st WQ)|]. split; [exact (wq_cur st WQ)| exact (wq_apend st WQ)].
Qed.
Lemma RTWF_ofq : forall st, RTWFq st -> qc_bytes (st_qthread st) <= QUAR_MAX_CACHE -> qc_bytes (st_qglobal st) <= QUAR_MAX_SIZE -> RTWF st.
Proof.
  intros st (W1 & W2 & W3 & W4 & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & W6 & W7) B1 B2.
  constructor; try assumption. constructor; assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qelems_q_set : forall st qt qg ap qp tmp cur,
  qelems (q_set st qt qg ap qp tmp cur) = flat_map qb_elems (qt ++ qg ++ tmp) ++ flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) cur.
Proof. intros. destruct st. reflexivity. Qed.
Lemma qall_q_set : forall st qt qg ap qp tmp cur, qall (q_set st qt qg ap qp tmp cur) = qt ++ qg ++ tmp ++ map fst cur.
Proof. intros. destruct st. reflexivity. Qed.
Lemma all_blocks_q_set : forall st qt qg ap qp tmp cur,
  all_blocks (q_set st qt qg ap qp tmp cur) = st_lb st ++ qelems (q_set st qt qg ap qp tmp cur) ++ qp.
Proof. intros. destruct st. reflexivity. Qed.
Lemma qelems_eq : forall st, qelems st = flat_map qb_elems (st_qthread st ++ st_qglobal st ++ st_qtmp st)
                                        ++ flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) (st_qcur st).
Proof. intros. reflexivity. Qed.
Lemma qall_eq : forall st, qall st = st_qthread st ++ st_qglobal st ++ st_qtmp st ++ map fst (st_qcur st).
Proof. intros. reflexivity. Qed.
Lemma all_blocks_eq : forall st, all_blocks st = st_lb st ++ qelems st ++ st_qpend st.
Proof. intros. reflexivity. Qed.

Lemma flat_map_app' : forall {A B} (f : A -> list B) l l', flat_map f (l ++ l') = flat_map f l ++ flat_map f l'.
Proof. intros. apply flat_map_app. Qed.
Lemma Permutation_flat_map' : forall {A B} (f : A -> list B) l l', Permutation l l' -> Permutation (flat_map f l) (flat_map f l').
Proof.
  intros A B f l l' H. induction H as [|x l l' H IH|x y l|l l' l'' H1 IH1 H2 IH2].
  - constructor.
  - cbn. apply Permutation_app_head. exact IH.
  - cbn. rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm.
  - eapply Permutation_trans; eauto.
Qed.

(* [comment removed for export] *)
Definition cf (c : Z) : Z * Z -> bool := fun b => bprim (snd b) && (pclass (snd b) =? c).
Lemma used_cptrs_eq : forall st c,
  used_cptrs st c = avail_cptrs st c ++ live_cptrs st c
                    ++ map (fun b => b_cptr st (fst b) (snd b)) (List.filter (cf c) (qelems st))
                    ++ map (fun b => b_cptr st (fst b) (snd b)) (List.filter (cf c) (st_qpend st))
                    ++ (if c =? 24 then map (fun a => (a - rbeg st 24) / 16) (map qb_addr (qall st)) else [])
                    ++ map snd (List.filter (fun ck => fst ck =? c) (st_apend st)).
Proof. intros. reflexivity. Qed.
Lemma b_cptr_q_set : forall st qt qg ap qp tmp cur A n, b_cptr (q_set st qt qg ap qp tmp cur) A n = b_cptr st A n.
Proof. intros. destruct st. reflexivity. Qed.
Lemma rbeg_q_set : forall st qt qg ap qp tmp cur c, rbeg (q_set st qt qg ap qp tmp cur) c = rbeg st c.
Proof. intros. destruct st. reflexivity. Qed.
Lemma carved_q_set : forall st qt qg ap qp tmp cur c k, carved_cptr (q_set st qt qg ap qp tmp cur) c k <-> carved_cptr st c k.
Proof. intros. destruct st. split; intros H; exact H. Qed.
Lemma ncarved_q_set : forall st qt qg ap qp tmp cur c, ncarved (q_set st qt qg ap qp tmp cur) c = ncarved st c.
Proof. intros. destruct st. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QSTEP.
Variable st : rtstate.
Variables (qt qg : list qbatch) (ap qp : list (Z * Z)) (tmp : list qbatch) (cur : list (qbatch * Z)).
Let st' := q_set st qt qg ap qp tmp cur.
Hypothesis WF : RTWFq st.
(* [comment removed for export] *)
Hypothesis USED : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st' c).
(* [comment removed for export] *)
Variable gone : list (Z * Z).
Hypothesis BLK : Permutation (all_blocks st) (gone ++ all_blocks st').
Hypothesis GONEP : Forall (fun b => bprim (snd b) = true) gone.
(* [comment removed for export] *)
Hypothesis QB : forall b, In b (qall st') -> qb_count b <= QBATCH_CAP /\ exists k, carved_cptr st 24 k /\ qb_addr b = cptr_addr st 24 k.
Hypothesis QT : forall b, In b qt -> 1 <= qb_count b.
Hypothesis QC : forall bd, In bd cur -> 0 <= snd bd <= qb_count (fst bd).
Hypothesis QA : forall ck, In ck ap -> 1 <= fst ck < KNUMCLASSES.
Hypothesis QR : qc_bytes qg + qc_bytes tmp + qc_bytes (map fst cur) <= QREC_MAX.
Hypothesis QI : zlen ap <= 1 /\ zlen qp <= 1.

Lemma qstep_in_blocks : forall b, In b (all_blocks st') -> In b (all_blocks st).
Proof. intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact BLK|]. apply in_or_app. right. exact Hb. Qed.

Theorem RTWFq_qstep : RTWFq st'.
Proof.
  destruct WF as (WB & WC & WK & WS & WQ & WD & WFS).
  assert (SAME := q_set_same st qt qg ap qp tmp cur). cbn zeta in SAME.
  destruct SAME as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - (* [comment removed for export] *) subst st'. destruct st; destruct WB; constructor; assumption.
  - intros c Hc. pose proof (WC c Hc) as W. subst st'. destruct st. destruct W; constructor; try assumption.
    + intros j Hj. apply wc_used_carved. eapply Permutation_in; [apply Permutation_sym; apply USED; exact Hc| exact Hj].
    + eapply Permutation_NoDup; [apply USED; exact Hc| exact wc_used_nodup].
    + unfold zlen in *. rewrite <- (Permutation_length (USED c Hc)). exact wc_used_all.
  - constructor.
    + intros b Hb. pose proof (wk_block st WK b (qstep_in_blocks b Hb)) as X. subst st'. destruct st. exact X.
    + pose proof (Permutation_NoDup (Permutation_map fst BLK) (wk_nodup st WK)) as ND. rewrite map_app in ND.
      exact (NoDup_app_remove_l _ _ ND).
  - destruct WS as [N1 N2 N3 N4 N5]. subst st'. destruct st. constructor; try assumption.
    + intros e He. destruct (N3 e He) as (X1 & X2 & X3 & X4). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
      destruct X4 as [X4|X4]; [| right; exact X4]. left.
      pose proof (Permutation_in _ BLK X4) as Y. apply in_app_iff in Y as [Y|Y]; [| exact Y].
      exfalso. pose proof (proj1 (Forall_forall _ _) GONEP _ Y) as Z1. cbn [snd] in Z1. rewrite X1 in Z1. discriminate.
    + intros e He. destruct (N4 e He) as [T1 T2]. split; [exact T1|]. intros C. apply T2.
      eapply Permutation_in; [apply Permutation_sym; exact BLK|]. apply in_or_app. right. exact C.
  - split; [| split; [| split; [| split; [| split]]]].
    + intros b Hb. destruct (QB b Hb) as [B1 (k & B2 & B3)]. split; [exact B1|]. exists k. subst st'. destruct st. split; [exact B2| exact B3].
    + subst st'. destruct st. exact QT.
    + subst st'. destruct st. exact QR.
    + subst st'. destruct st. exact QI.
    + subst st'. destruct st. exact QC.
    + subst st'. destruct st. exact QA.
  - subst st'. destruct st; destruct WD; constructor; assumption.
  - subst st'. destruct st; destruct WFS; constructor; assumption.
Qed.
End QSTEP.

Lemma zlen_remove_first_le : forall x (l : list (Z * Z)), zlen (remove_first ck_eqb x l) <= zlen l.
Proof.
  intros x l. induction l as [|y l IH]; [cbn; lia|]. cbn [remove_first]. destruct (ck_eqb x y); rewrite ?zlen_cons; lia.
Qed.

Lemma last_In : forall {X} (l : list X) d, l <> [] -> In (last l d) l.
Proof. intros X l d NE. rewrite (app_removelast_last d NE) at 2. apply in_or_app. right. left. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma rt_prov_q_set_gone : forall st qt qg ap qp tmp cur gone, let st' := q_set st qt qg ap qp tmp cur in
  Permutation (qelems st ++ st_qpend st) (gone ++ qelems st' ++ qp) ->
  rt_prov st' = rt_prov st - prov_nb st - prov_q st + prov_nb st' + prov_q st' - zsum (map (fun b => rp (snd b)) gone).
Proof.
  intros st qt qg ap qp tmp cur gone st' P.
  assert (E1 : prov_classes st' = prov_classes st) by (subst st'; destruct st; reflexivity).
  assert (E4 : prov_ptr st' = prov_ptr st) by (subst st'; destruct st; reflexivity).
  assert (E5 : prov_live st' = prov_live st) by (subst st'; destruct st; reflexivity).
  assert (E6 : prov_quar st = prov_quar st' + zsum (map (fun b => rp (snd b)) gone)).
  { unfold prov_quar. replace (st_qpend st') with qp by (subst st'; destruct st; reflexivity).
    rewrite (zsum_map_perm _ _ _ P), !map_app, !zsum_app. lia. }
  assert (E7 : prov_depot st' = prov_depot st) by (subst st'; destruct st; reflexivity).
  assert (E8 : prov_slots st' = prov_slots st) by (subst st'; destruct st; reflexivity).
  assert (E9 : prov_l24 st' = prov_l24 st) by (subst st'; destruct st; reflexivity).
  assert (E10 : prov_emb st' = prov_emb st) by (subst st'; destruct st; reflexivity).   (* [comment removed for export] *)
  unfold rt_prov. rewrite E1, E4, E5, E7, E8, E9. lia.
Qed.
Lemma rt_prov_q_set : forall st qt qg ap qp tmp cur, let st' := q_set st qt qg ap qp tmp cur in
  Permutation (qelems st ++ st_qpend st) (qelems st' ++ qp) ->
  rt_prov st' = rt_prov st - prov_nb st - prov_q st + prov_nb st' + prov_q st'.
Proof.
  intros st qt qg ap qp tmp cur st' P. pose proof (rt_prov_q_set_gone st qt qg ap qp tmp cur [] P) as E. cbn [map zsum fold_right] in E.
  subst st'. unfold zsum in E. cbn [fold_right] in E. lia.
Qed.

Lemma thread_room_le : forall st, RTWFq st -> st_qthread st <> [] -> 0 <= thread_room st <= QBATCH_CAP - 1.
Proof.
  intros st (_ & _ & _ & _ & (Q1 & Q2 & _) & _) NE. unfold thread_room. destruct (st_qthread st) as [|b0 q0] eqn:E; [congruence|].
  assert (HIN : In (last (b0 :: q0) (mkQB 0 [])) (st_qthread st)) by (rewrite E; apply last_In; discriminate).
  pose proof (Q2 _ ltac:(rewrite <- E; exact HIN)) as C1. pose proof (proj1 (Q1 _ ltac:(unfold qall; apply in_or_app; left; exact HIN))) as C2. lia.
Qed.
Lemma prov_nb_bound : forall st, RTWFq st -> 0 <= prov_nb st <= NB.
Proof.
  intros st WF. pose proof (thread_room_le st WF) as TR. unfold prov_nb, NB, SLOTP, QBATCH_CAP in *.
  destruct (st_qthread st); [lia|]. specialize (TR ltac:(discriminate)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section QI.
Variables (a1 a2 a3 : Z) (a4 : list region_st) (a5 : bool) (a6 : list (list Z)) (a7 a8 : Z) (a9 : list (Z * Z))
          (a10 a11 : list qbatch) (a12 : depot_st) (a13 a14 : list (list Z)) (a15 : Z) (a16 : list Z) (a17 : list fframe)
          (a18 a19 : Z) (a20 : tls_st) (a21 : list (Z * Z)) (a22 : bool) (LB : list (Z * Z))
          (AP SP QP : list (Z * Z)) (b4 : list qbatch) (b5 : list (qbatch * Z)).
Let st := mkRT a1 a2 a3 a4 a5 a6 a7 a8 a9 a10 a11 a12 a13 a14 a15 a16 a17 a18 a19 a20 a21 a22 LB AP SP QP b4 b5.
Hypothesis WF : RTWFq st.
Let g := fun b0 : Z * Z => b_cptr st (fst b0) (snd b0).

(* [comment removed for export] *)
Section ENQ_LAST.
Variables (A n : Z) (q : list qbatch) (b : qbatch).
Hypothesis HIN : In (A, n) QP.
Hypothesis HQ : a10 = q ++ [b].
Hypothesis ROOM : qb_count b < QBATCH_CAP.
Hypothesis Hn : 0 <= n.
Let st1 := st_enq_last st A n.

Lemma enq_last_eq : st1 = q_set st (q ++ [qb_push b (A, n)]) a11 AP (remove_first ck_eqb (A, n) QP) b4 b5.
Proof. subst st1. unfold st_enq_last. cbn [st_qthread st_qglobal st_apend st_qpend st_qtmp st_qcur st]. rewrite HQ, upd_last_snoc. reflexivity. Qed.

Lemma enq_last_qelems : Permutation (qelems st1) ((A, n) :: qelems st).
Proof.
  rewrite enq_last_eq. cbn -[qb_push skipn Z.to_nat]. rewrite HQ. rewrite !flat_map_app'. cbn [flat_map qb_push qb_elems].
  rewrite !app_nil_r. rewrite <- !app_assoc.
  set (X := flat_map qb_elems q). set (Y := qb_elems b).
  set (R := flat_map qb_elems a11 ++ flat_map qb_elems b4 ++ flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) b5).
  change (X ++ Y ++ [(A, n)] ++ R) with (X ++ Y ++ (A, n) :: R).
  rewrite (app_assoc X Y ((A, n) :: R)), (app_assoc X Y R). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma enq_last_qall : map qb_addr (qall st1) = map qb_addr (qall st).
Proof. rewrite enq_last_eq. cbn -[qb_push]. rewrite HQ, !map_app. cbn [map qb_push qb_addr]. reflexivity. Qed.

Lemma enq_last_used : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st1 c).
Proof.
  intros c Hc. rewrite !used_cptrs_eq.
  change (avail_cptrs st1 c) with (avail_cptrs st c). change (live_cptrs st1 c) with (live_cptrs st c).
  change (rbeg st1 24) with (rbeg st 24). change (st_apend st1) with AP. change (st_qpend st) with QP.
  change (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)).
  set (h := fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)) in *.
  replace (st_qpend st1) with (remove_first ck_eqb (A, n) QP) by (rewrite enq_last_eq; reflexivity).
  rewrite enq_last_qall. do 2 apply Permutation_app_head.
  rewrite !app_assoc. do 2 apply Permutation_app_tail.
  destruct (cf c (A, n)) eqn:EF.
  - destruct (remove_first_filter_true (cf c) (A, n) QP EF) as [P|N]; [| exfalso; exact (N HIN)].
    cbn [List.filter] in P. rewrite EF in P.
    apply Permutation_trans with (map h (List.filter (cf c) ((A, n) :: qelems st)) ++ map h (List.filter (cf c) (remove_first ck_eqb (A, n) QP))).
    + cbn [List.filter]. rewrite EF. cbn [map].
      apply Permutation_trans with (map h (List.filter (cf c) (qelems st)) ++ h (A, n) :: map h (List.filter (cf c) (remove_first ck_eqb (A, n) QP))).
      * apply Permutation_app_head. rewrite <- map_cons. apply Permutation_map. exact P.
      * apply Permutation_sym. apply Permutation_middle.
    + apply Permutation_app_tail. apply Permutation_map. apply Permutation_filter'. apply Permutation_sym. exact enq_last_qelems.
  - rewrite (filter_remove_first_false (cf c) (A, n) QP EF). apply Permutation_app_tail. apply Permutation_map.
    apply Permutation_trans with (List.filter (cf c) ((A, n) :: qelems st)); [cbn [List.filter]; rewrite EF; apply Permutation_refl|].
    apply Permutation_filter'. apply Permutation_sym. exact enq_last_qelems.
Qed.

Lemma enq_last_blocks : Permutation (all_blocks st) ([] ++ all_blocks st1).
Proof.
  cbn [app]. rewrite !all_blocks_eq. change (st_lb st1) with (st_lb st).
  replace (st_qpend st1) with (remove_first ck_eqb (A, n) QP) by (rewrite enq_last_eq; reflexivity). change (st_qpend st) with QP.
  apply Permutation_app_head.
  apply Permutation_trans with (qelems st ++ (A, n) :: remove_first ck_eqb (A, n) QP).
  - apply Permutation_app_head. apply remove_first_perm. exact HIN.
  - apply Permutation_trans with (((A, n) :: qelems st) ++ remove_first ck_eqb (A, n) QP).
    + apply Permutation_sym. cbn [app]. apply Permutation_middle.
    + apply Permutation_app_tail. apply Permutation_sym. exact enq_last_qelems.
Qed.

Theorem RTWFq_enq_last : RTWFq st1.
Proof.
  rewrite enq_last_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _).
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. rewrite <- enq_last_eq. apply enq_last_used. exact Hc.
  - rewrite <- enq_last_eq. apply enq_last_blocks.
  - constructor.
  - intros b' Hb'. rewrite qall_q_set in Hb'. unfold qall in Q1. cbn [st_qthread st_qglobal st_qtmp st_qcur st] in Q1. rewrite HQ in Q1.
    assert (CASE : b' = qb_push b (A, n) \/ In b' ((q ++ [b]) ++ a11 ++ b4 ++ map fst b5)).
    { rewrite !in_app_iff in Hb'. cbn [In] in Hb'. rewrite !in_app_iff. cbn [In].
      destruct Hb' as [[Hq|[E|[]]]|R]; [right; left; left; exact Hq| left; symmetry; exact E| right; right; exact R]. }
    destruct CASE as [->|IN].
    + destruct (Q1 b ltac:(rewrite !in_app_iff; cbn [In]; tauto)) as [C1 (k & C2 & C3)].
      split; [rewrite qb_count_push; lia|]. exists k. split; [exact C2| exact C3].
    + exact (Q1 b' IN).
  - intros b' Hb'. cbn [st_qthread st] in Q2. rewrite HQ in Q2. apply in_app_iff in Hb' as [Hb'|[<-|[]]].
    + apply Q2. apply in_or_app. left. exact Hb'.
    + rewrite qb_count_push. pose proof (Q2 b ltac:(apply in_or_app; right; left; reflexivity)). lia.
  - exact Q3.
  - exact Q4.
  - exact Q5.
  - destruct Q6 as [I1 I2]. split; [exact I1|]. pose proof (zlen_remove_first_le (A, n) QP). cbn [st_qpend st] in I2. lia.
Qed.

Theorem rt_prov_enq_last : rt_prov st1 <= rt_prov st + fp n.
Proof.
  rewrite enq_last_eq.
  rewrite (rt_prov_q_set st _ _ _ _ _ _).
  2:{ rewrite <- enq_last_eq. change (st_qpend st) with QP.
      apply Permutation_trans with (((A, n) :: qelems st) ++ remove_first ck_eqb (A, n) QP).
      - apply Permutation_trans with (qelems st ++ (A, n) :: remove_first ck_eqb (A, n) QP);
          [apply Permutation_app_head; apply remove_first_perm; exact HIN| apply Permutation_sym; cbn [app]; apply Permutation_middle].
      - apply Permutation_app_tail. apply Permutation_sym. exact enq_last_qelems. }
  (* [comment removed for export] *)
  pose proof (thread_room_le st WF ltac:(cbn [st_qthread st]; rewrite HQ; destruct q; discriminate)) as TR.
  unfold prov_nb, prov_q, thread_room in *. cbn [st_qthread st] in *. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)).
  rewrite HQ in *. rewrite !last_last in *.
  assert (NE1 : q ++ [qb_push b (A, n)] <> []) by (destruct q; discriminate).
  assert (NE0 : q ++ [b] <> []) by (destruct q; discriminate).
  destruct (q ++ [qb_push b (A, n)]) eqn:E1; [congruence|]. rewrite <- E1.
  destruct (q ++ [b]) eqn:E0; [congruence|]. rewrite <- E0 in *.
  rewrite ?last_last, qb_count_push, !qc_bytes_app, !qc_bytes_cons, qc_bytes_nil, qb_size_push.
  pose proof (qc_bytes_nonneg q) as B0. pose proof (qc_bytes_nonneg [b]) as B1. rewrite qc_bytes_cons, qc_bytes_nil in B1.
  unfold NB, SLOTP, QBATCH_CAP, fp in *.
  Z.div_mod_to_equations. nia.
Qed.
End ENQ_LAST.

(* [comment removed for export] *)
Section ENQ_NEW.
Variables (k A n : Z).
Hypothesis HIN : In (A, n) QP.
Hypothesis HK : In (24, k) AP.
Hypothesis Hn : 0 <= n.
Let nb := mkQB (cptr_addr st 24 k) [(A, n)].
Let st1 := st_enq_new st k A n.

Lemma enq_new_eq : st1 = q_set st (a10 ++ [nb]) a11 (remove_first ck_eqb (24, k) AP) (remove_first ck_eqb (A, n) QP) b4 b5.
Proof. reflexivity. Qed.

Lemma enq_new_qelems : Permutation (qelems st1) ((A, n) :: qelems st).
Proof.
  rewrite enq_new_eq. cbn -[skipn Z.to_nat]. rewrite !flat_map_app'. cbn [flat_map qb_elems].
  rewrite <- !app_assoc. cbn [app].
  set (X := flat_map qb_elems a10).
  set (R := flat_map qb_elems a11 ++ flat_map qb_elems b4 ++ flat_map (fun bd : qbatch * Z => skipn (Z.to_nat (snd bd)) (qb_elems (fst bd))) b5).
  apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma enq_new_qall : Permutation (map qb_addr (qall st1)) (cptr_addr st 24 k :: map qb_addr (qall st)).
Proof.
  rewrite enq_new_eq. cbn -[cptr_addr]. rewrite !map_app. cbn [map qb_addr]. rewrite <- !app_assoc. cbn [app].
  apply Permutation_sym. apply Permutation_middle.
Qed.

Lemma enq_new_used : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st1 c).
Proof.
  intros c Hc. rewrite !used_cptrs_eq.
  change (avail_cptrs st1 c) with (avail_cptrs st c). change (live_cptrs st1 c) with (live_cptrs st c).
  change (rbeg st1 24) with (rbeg st 24). change (st_qpend st) with QP. change (st_apend st) with AP.
  change (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)).
  set (h := fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)) in *.
  replace (st_qpend st1) with (remove_first ck_eqb (A, n) QP) by (rewrite enq_new_eq; reflexivity).
  replace (st_apend st1) with (remove_first ck_eqb (24, k) AP) by (rewrite enq_new_eq; reflexivity).
  do 2 apply Permutation_app_head.
  (* [comment removed for export] *)
  assert (PQ : Permutation (map h (List.filter (cf c) (qelems st)) ++ map h (List.filter (cf c) QP))
                           (map h (List.filter (cf c) (qelems st1)) ++ map h (List.filter (cf c) (remove_first ck_eqb (A, n) QP)))).
  { destruct (cf c (A, n)) eqn:EF.
    - destruct (remove_first_filter_true (cf c) (A, n) QP EF) as [P|N]; [| exfalso; exact (N HIN)].
      cbn [List.filter] in P. rewrite EF in P.
      apply Permutation_trans with (map h (List.filter (cf c) ((A, n) :: qelems st)) ++ map h (List.filter (cf c) (remove_first ck_eqb (A, n) QP))).
      + cbn [List.filter]. rewrite EF. cbn [map].
        apply Permutation_trans with (map h (List.filter (cf c) (qelems st)) ++ h (A, n) :: map h (List.filter (cf c) (remove_first ck_eqb (A, n) QP))).
        * apply Permutation_app_head. rewrite <- map_cons. apply Permutation_map. exact P.
        * apply Permutation_sym. apply Permutation_middle.
      + apply Permutation_app_tail. apply Permutation_map. apply Permutation_filter'. apply Permutation_sym. exact enq_new_qelems.
    - rewrite (filter_remove_first_false (cf c) (A, n) QP EF). apply Permutation_app_tail. apply Permutation_map.
      apply Permutation_trans with (List.filter (cf c) ((A, n) :: qelems st)); [cbn [List.filter]; rewrite EF; apply Permutation_refl|].
      apply Permutation_filter'. apply Permutation_sym. exact enq_new_qelems. }
  (* [comment removed for export] *)
  lazymatch goal with |- Permutation (?Q ++ ?P ++ ?B ++ ?Ap) (?Q1 ++ ?P1 ++ ?B1 ++ ?Ap1) =>
    apply (Permutation_trans (l' := (Q1 ++ P1) ++ (B ++ Ap)));
    [ rewrite (app_assoc Q P (B ++ Ap)); apply Permutation_app_tail; exact PQ
    | rewrite (app_assoc Q1 P1 (B1 ++ Ap1)); apply Permutation_app_head ] end.
  destruct (Z.eqb_spec c 24) as [->|NE].
  - destruct (remove_first_filter_true (fun ck : Z * Z => fst ck =? 24) (24, k) AP eq_refl) as [P|N]; [| exfalso; exact (N HK)].
    cbn [List.filter fst Z.eqb Pos.eqb] in P.
    apply Permutation_trans with (map (fun a : Z => (a - rbeg st 24) / 16) (map qb_addr (qall st)) ++ k :: map snd (List.filter (fun ck : Z * Z => fst ck =? 24) (remove_first ck_eqb (24, k) AP))).
    + apply Permutation_app_head. change k with (snd (24, k)) at 1. rewrite <- map_cons. apply Permutation_map. exact P.
    + apply Permutation_trans with ((k :: map (fun a : Z => (a - rbeg st 24) / 16) (map qb_addr (qall st))) ++ map snd (List.filter (fun ck : Z * Z => fst ck =? 24) (remove_first ck_eqb (24, k) AP))).
      * apply Permutation_sym. cbn [app]. apply Permutation_middle.
      * apply Permutation_app_tail. replace k with ((cptr_addr st 24 k - rbeg st 24) / 16) at 1 by (unfold cptr_addr; Z.div_mod_to_equations; lia).
        change ((cptr_addr st 24 k - rbeg st 24) / 16 :: map (fun a : Z => (a - rbeg st 24) / 16) (map qb_addr (qall st)))
          with (map (fun a : Z => (a - rbeg st 24) / 16) (cptr_addr st 24 k :: map qb_addr (qall st))).
        apply Permutation_map. apply Permutation_sym. exact enq_new_qall.
  - rewrite (filter_remove_first_false (fun ck : Z * Z => fst ck =? c) (24, k) AP) by (cbn [fst]; apply Z.eqb_neq; lia). apply Permutation_refl.
Qed.

Lemma enq_new_blocks : Permutation (all_blocks st) ([] ++ all_blocks st1).
Proof.
  cbn [app]. rewrite !all_blocks_eq. change (st_lb st1) with (st_lb st).
  replace (st_qpend st1) with (remove_first ck_eqb (A, n) QP) by (rewrite enq_new_eq; reflexivity). change (st_qpend st) with QP.
  apply Permutation_app_head.
  apply Permutation_trans with (qelems st ++ (A, n) :: remove_first ck_eqb (A, n) QP).
  - apply Permutation_app_head. apply remove_first_perm. exact HIN.
  - apply Permutation_trans with (((A, n) :: qelems st) ++ remove_first ck_eqb (A, n) QP).
    + apply Permutation_sym. cbn [app]. apply Permutation_middle.
    + apply Permutation_app_tail. apply Permutation_sym. exact enq_new_qelems.
Qed.

Theorem RTWFq_enq_new : RTWFq st1.
Proof.
  rewrite enq_new_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _).
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. rewrite <- enq_new_eq. apply enq_new_used. exact Hc.
  - rewrite <- enq_new_eq. apply enq_new_blocks.
  - constructor.
  - intros b' Hb'. rewrite qall_q_set in Hb'. unfold qall in Q1. cbn [st_qthread st_qglobal st_qtmp st_qcur st] in Q1.
    assert (CASE : b' = nb \/ In b' (a10 ++ a11 ++ b4 ++ map fst b5)).
    { rewrite !in_app_iff in Hb'. cbn [In] in Hb'. rewrite !in_app_iff.
      destruct Hb' as [[Hq|[E|[]]]|R]; [right; left; exact Hq| left; symmetry; exact E| right; right; exact R]. }
    destruct CASE as [->|IN].
    + split; [subst nb; unfold qb_count, QBATCH_CAP; cbn; lia|]. exists k. split; [| reflexivity].
      apply (wc_used_carved st 24 (WC 24 ltac:(unfold KNUMCLASSES; lia))). unfold used_cptrs. rewrite !in_app_iff. do 5 right.
      unfold apend_cptrs. apply in_map_iff. exists (24, k). split; [reflexivity|]. apply filter_In. split; [exact HK| reflexivity].
    + exact (Q1 b' IN).
  - intros b' Hb'. apply in_app_iff in Hb' as [Hb'|[<-|[]]]; [exact (Q2 b' Hb')|]. subst nb. unfold qb_count. cbn. lia.
  - exact Q3.
  - intros ck Hck. apply Q4. eapply remove_first_In. exact Hck.
  - exact Q5.
  - destruct Q6 as [I1 I2]. cbn [st_apend st_qpend st] in I1, I2.
    pose proof (zlen_remove_first_le (24, k) AP). pose proof (zlen_remove_first_le (A, n) QP). split; lia.
Qed.

(* [comment removed for export] *)
Hypothesis FULL : a10 = [] \/ thread_room st = 0.
Theorem rt_prov_enq_new : rt_prov st1 + 2 * csize 24 <= rt_prov st + fp n.
Proof.
  rewrite enq_new_eq.
  rewrite (rt_prov_q_set st _ _ _ _ _ _).
  2:{ rewrite <- enq_new_eq. change (st_qpend st) with QP.
      apply Permutation_trans with (((A, n) :: qelems st) ++ remove_first ck_eqb (A, n) QP).
      - apply Permutation_trans with (qelems st ++ (A, n) :: remove_first ck_eqb (A, n) QP);
          [apply Permutation_app_head; apply remove_first_perm; exact HIN| apply Permutation_sym; cbn [app]; apply Permutation_middle].
      - apply Permutation_app_tail. apply Permutation_sym. exact enq_new_qelems. }
  assert (PNB : prov_nb st = NB).
  { unfold prov_nb. destruct FULL as [E|R]; cbn [st_qthread st]; [rewrite E; reflexivity|]. rewrite R. destruct a10; [reflexivity|]. unfold NB, SLOTP. lia. }
  rewrite PNB. unfold prov_nb, prov_q, thread_room. cbn [st_qthread st]. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)).
  assert (NE1 : a10 ++ [nb] <> []) by (destruct a10; discriminate).
  destruct (a10 ++ [nb]) eqn:E1; [congruence|]. rewrite <- E1. rewrite last_last.
  rewrite !qc_bytes_app, qc_bytes_cons, qc_bytes_nil. subst nb. rewrite qb_size_one. unfold qb_count. cbn [qb_elems length Z.of_nat Pos.of_succ_nat].
  pose proof (qc_bytes_nonneg a10) as B0. change (csize 24) with 8192.
  unfold NB, SLOTP, QBATCH_CAP, QBATCH_SIZE, fp in *.
  Z.div_mod_to_equations. nia.
Qed.
End ENQ_NEW.

(* [comment removed for export] *)
Section DRAIN.
Let st1 := st_drain st.
Lemma drain_eq : st1 = q_set st [] (a11 ++ a10) AP QP b4 b5. Proof. reflexivity. Qed.

Lemma drain_qelems : Permutation (qelems st1) (qelems st).
Proof.
  rewrite drain_eq. cbn -[skipn Z.to_nat]. rewrite !flat_map_app'. rewrite !app_assoc. do 2 apply Permutation_app_tail. apply Permutation_app_comm.
Qed.
Lemma drain_qall : Permutation (map qb_addr (qall st1)) (map qb_addr (qall st)).
Proof. rewrite drain_eq. cbn. rewrite !map_app. rewrite !app_assoc. do 2 apply Permutation_app_tail. apply Permutation_app_comm. Qed.

Lemma drain_used : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st1 c).
Proof.
  intros c Hc. rewrite !used_cptrs_eq.
  change (avail_cptrs st1 c) with (avail_cptrs st c). change (live_cptrs st1 c) with (live_cptrs st c).
  change (rbeg st1 24) with (rbeg st 24). change (st_qpend st1) with (st_qpend st). change (st_apend st1) with (st_apend st).
  change (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)).
  do 2 apply Permutation_app_head. apply Permutation_app; [apply Permutation_map; apply Permutation_filter'; apply Permutation_sym; exact drain_qelems|].
  apply Permutation_app_head. apply Permutation_app_tail.
  destruct (c =? 24); [| apply Permutation_refl]. apply Permutation_map. apply Permutation_sym. exact drain_qall.
Qed.

Hypothesis DQR : qc_bytes a11 + qc_bytes a10 <= QREC_MAX.
Hypothesis DT : b4 = [].
Hypothesis DC : b5 = [].
Theorem RTWFq_drain : RTWFq st1.
Proof.
  rewrite drain_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _).
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. rewrite <- drain_eq. apply drain_used. exact Hc.
  - cbn [app]. rewrite !all_blocks_eq. rewrite <- drain_eq. change (st_lb st1) with (st_lb st). change (st_qpend st1) with (st_qpend st).
    apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_sym. exact drain_qelems.
  - constructor.
  - intros b' Hb'. apply Q1. unfold qall. cbn [st_qthread st_qglobal st_qtmp st_qcur st]. rewrite qall_q_set in Hb'.
    cbn [app] in Hb'. rewrite !in_app_iff.
    apply in_app_iff in Hb' as [Hb'|Hb']; [apply in_app_iff in Hb' as [Hb'|Hb']; tauto| apply in_app_iff in Hb' as [Hb'|Hb']; tauto].
  - intros b' [].
  - exact Q3.
  - exact Q4.
  - rewrite DT, DC, qc_bytes_app. cbn [map]. rewrite qc_bytes_nil. lia.
  - exact Q6.
Qed.

Hypothesis BIG : 2^20 < qc_bytes a10.
Theorem rt_prov_drain : rt_prov st1 <= rt_prov st.
Proof.
  rewrite drain_eq.
  rewrite (rt_prov_q_set st _ _ _ _ _ _).
  2:{ rewrite <- drain_eq. change (st_qpend st) with QP. apply Permutation_app_tail. apply Permutation_sym. exact drain_qelems. }
  pose proof (prov_nb_bound st WF) as NB0.
  unfold prov_q. cbn [st_qthread st]. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). rewrite qc_bytes_nil.
  assert (PNB1 : prov_nb (q_set st [] (a11 ++ a10) AP QP b4 b5) = NB) by (unfold prov_nb; rewrite (proj1 (q_set_fields st _ _ _ _ _ _)); reflexivity).
  rewrite PNB1. unfold NB in *. Z.div_mod_to_equations. nia.
Qed.
End DRAIN.

(* [comment removed for export] *)
Section MERGE.
Variables (pre : list qbatch) (cur nxt : qbatch) (post : list qbatch).
Hypothesis HG : a11 = pre ++ cur :: nxt :: post.
Hypothesis CAP : qb_count cur + qb_count nxt <= QBATCH_CAP.
Let st1 := st_merge st pre cur nxt post.
Lemma merge_eq : st1 = q_set st a10 (pre ++ qb_absorb cur nxt :: post) AP QP (b4 ++ [mkQB (qb_addr nxt) []]) b5. Proof. reflexivity. Qed.

Lemma merge_qelems : qelems st1 = qelems st.
Proof.
  rewrite merge_eq. cbn -[skipn Z.to_nat qb_absorb]. rewrite HG. rewrite !flat_map_app'. cbn [flat_map qb_absorb qb_elems].
  rewrite !app_nil_r, <- !app_assoc. reflexivity.
Qed.
Lemma merge_qall : Permutation (map qb_addr (qall st1)) (map qb_addr (qall st)).
Proof.
  rewrite merge_eq. cbn -[qb_absorb]. rewrite HG, !map_app. cbn [map qb_addr qb_absorb].
  rewrite <- !app_assoc. cbn [app]. apply Permutation_app_head. apply Permutation_app_head. apply perm_skip.
  (* [comment removed for export] *)
  set (P1 := map qb_addr post). set (P2 := map qb_addr b4). set (P3 := map qb_addr (map fst b5)). set (x := qb_addr nxt).
  rewrite (app_assoc P1 P2 (x :: P3)), (app_assoc P1 P2 P3). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma merge_used : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st1 c).
Proof.
  intros c Hc. rewrite !used_cptrs_eq.
  change (avail_cptrs st1 c) with (avail_cptrs st c). change (live_cptrs st1 c) with (live_cptrs st c).
  change (rbeg st1 24) with (rbeg st 24). change (st_qpend st1) with (st_qpend st). change (st_apend st1) with (st_apend st).
  change (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)).
  rewrite merge_qelems. do 4 apply Permutation_app_head. apply Permutation_app_tail.
  destruct (c =? 24); [| apply Permutation_refl]. apply Permutation_map. apply Permutation_sym. exact merge_qall.
Qed.
Theorem RTWFq_merge : RTWFq st1.
Proof.
  rewrite merge_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _).
  unfold qall in Q1. cbn [st_qthread st_qglobal st_qtmp st_qcur st] in Q1. rewrite HG in Q1.
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. rewrite <- merge_eq. apply merge_used. exact Hc.
  - cbn [app]. rewrite !all_blocks_eq. rewrite <- merge_eq, merge_qelems. apply Permutation_refl.
  - constructor.
  - intros b' Hb'. rewrite qall_q_set in Hb'.
    Local Ltac q1 Q1 := apply Q1; rewrite !in_app_iff; cbn [In]; tauto.
    apply in_app_iff in Hb' as [Hb'|Hb']; [q1 Q1|].
    apply in_app_iff in Hb' as [Hb'|Hb'].
    + apply in_app_iff in Hb' as [Hb'|[<-|Hb']]; [q1 Q1| | q1 Q1].
      destruct (Q1 cur ltac:(rewrite !in_app_iff; cbn [In]; tauto)) as [_ (kk & C2 & C3)].
      split; [rewrite qb_count_absorb; exact CAP|]. exists kk. split; [exact C2| exact C3].
    + apply in_app_iff in Hb' as [Hb'|Hb']; [| q1 Q1].
      apply in_app_iff in Hb' as [Hb'|[<-|[]]]; [q1 Q1|].
      destruct (Q1 nxt ltac:(rewrite !in_app_iff; cbn [In]; tauto)) as [_ (kk & C2 & C3)].
      split; [unfold qb_count, QBATCH_CAP; cbn; lia|]. exists kk. split; [exact C2| exact C3].
  - exact Q2.
  - exact Q3.
  - exact Q4.
  - cbn [st_qglobal st_qtmp st_qcur st] in Q5. rewrite HG in Q5. rewrite !qc_bytes_app, !qc_bytes_cons in *. rewrite qc_bytes_nil.
    rewrite qb_size_absorb. unfold qb_size at 3. cbn [qb_elems fold_right]. lia.
  - exact Q6.
Qed.
Theorem rt_prov_merge : rt_prov st1 = rt_prov st.
Proof.
  rewrite merge_eq. rewrite (rt_prov_q_set st _ _ _ _ _ _).
  2:{ rewrite <- merge_eq, merge_qelems. apply Permutation_refl. }
  unfold prov_nb, prov_q, thread_room. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). cbn [st_qthread st]. lia.
Qed.
End MERGE.

(* [comment removed for export] *)
Section QPOP.
Variables (b : qbatch) (r : list qbatch).
Hypothesis HG : a11 = b :: r.
Let st1 := st_qpop st.
Lemma qpop_eq : st1 = q_set st a10 r AP QP (b4 ++ [b]) b5.
Proof. subst st1. unfold st_qpop. cbn [st_qglobal st]. rewrite HG. reflexivity. Qed.
Lemma qpop_qelems : Permutation (qelems st1) (qelems st).
Proof.
  rewrite qpop_eq. cbn -[skipn Z.to_nat]. rewrite HG, !flat_map_app'. cbn [flat_map]. rewrite app_nil_r.
  apply Permutation_app_tail. apply Permutation_app_head. rewrite <- ?app_assoc. rewrite (app_assoc (flat_map qb_elems r) (flat_map qb_elems b4) (qb_elems b)).
  eapply Permutation_trans; [apply Permutation_app_comm|]. rewrite <- ?app_assoc. apply Permutation_refl.
Qed.
Lemma qpop_qall : Permutation (map qb_addr (qall st1)) (map qb_addr (qall st)).
Proof.
  rewrite qpop_eq. cbn. rewrite HG, !map_app. cbn [map]. apply Permutation_app_head.
  rewrite <- !app_assoc. cbn [app].
  set (P1 := map qb_addr r). set (P2 := map qb_addr b4). set (P3 := map qb_addr (map fst b5)). set (x := qb_addr b).
  rewrite (app_assoc P1 P2 (x :: P3)), (app_assoc P1 P2 P3). apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma qpop_used : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st1 c).
Proof.
  intros c Hc. rewrite !used_cptrs_eq.
  replace (avail_cptrs st1 c) with (avail_cptrs st c) by (rewrite qpop_eq; reflexivity).
  replace (live_cptrs st1 c) with (live_cptrs st c) by (rewrite qpop_eq; reflexivity).
  replace (rbeg st1 24) with (rbeg st 24) by (rewrite qpop_eq; reflexivity).
  replace (st_qpend st1) with (st_qpend st) by (rewrite qpop_eq; reflexivity).
  replace (st_apend st1) with (st_apend st) by (rewrite qpop_eq; reflexivity).
  replace (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)) by (rewrite qpop_eq; reflexivity).
  do 2 apply Permutation_app_head. apply Permutation_app; [apply Permutation_map; apply Permutation_filter'; apply Permutation_sym; exact qpop_qelems|].
  apply Permutation_app_head. apply Permutation_app_tail.
  destruct (c =? 24); [| apply Permutation_refl]. apply Permutation_map. apply Permutation_sym. exact qpop_qall.
Qed.
Theorem RTWFq_qpop : RTWFq st1.
Proof.
  rewrite qpop_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _).
  unfold qall in Q1. cbn [st_qthread st_qglobal st_qtmp st_qcur st] in Q1. rewrite HG in Q1.
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. rewrite <- qpop_eq. apply qpop_used. exact Hc.
  - cbn [app]. rewrite !all_blocks_eq. rewrite <- qpop_eq.
    replace (st_lb st1) with (st_lb st) by (rewrite qpop_eq; reflexivity). replace (st_qpend st1) with (st_qpend st) by (rewrite qpop_eq; reflexivity).
    apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_sym. exact qpop_qelems.
  - constructor.
  - intros b' Hb'. rewrite qall_q_set in Hb'. apply Q1. rewrite !in_app_iff. cbn [In].
    apply in_app_iff in Hb' as [Hb'|Hb']; [tauto|]. apply in_app_iff in Hb' as [Hb'|Hb']; [tauto|].
    apply in_app_iff in Hb' as [Hb'|Hb']; [| tauto]. apply in_app_iff in Hb' as [Hb'|[<-|[]]]; tauto.
  - exact Q2.
  - exact Q3.
  - exact Q4.
  - cbn [st_qglobal st_qtmp st_qcur st] in Q5. rewrite HG in Q5. rewrite !qc_bytes_app, !qc_bytes_cons in *. rewrite qc_bytes_nil. lia.
  - exact Q6.
Qed.
Theorem rt_prov_qpop : rt_prov st1 = rt_prov st.
Proof.
  rewrite qpop_eq. rewrite (rt_prov_q_set st _ _ _ _ _ _).
  2:{ rewrite <- qpop_eq. replace (st_qpend st) with QP by reflexivity. apply Permutation_app_tail. apply Permutation_sym. exact qpop_qelems. }
  unfold prov_nb, prov_q, thread_room. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). cbn [st_qthread st]. lia.
Qed.
End QPOP.

(* [comment removed for export] *)
Section QSTART.
Variables (b : qbatch) (r : list qbatch).
Hypothesis HT : b4 = b :: r.
Hypothesis HC : b5 = [].
Let st1 := st_qstart st.
Lemma qstart_eq : st1 = q_set st a10 a11 AP QP r [(b, 0)].
Proof. subst st1. unfold st_qstart. cbn [st_qtmp st]. rewrite HT. reflexivity. Qed.
Lemma qstart_qelems : Permutation (qelems st1) (qelems st).
Proof.
  rewrite qstart_eq. cbn -[skipn Z.to_nat]. rewrite HT, HC, !flat_map_app'. cbn [flat_map Z.to_nat skipn fst snd]. rewrite !app_nil_r.
  rewrite <- !app_assoc. do 2 apply Permutation_app_head. apply Permutation_app_comm.
Qed.
Lemma qstart_qall : Permutation (map qb_addr (qall st1)) (map qb_addr (qall st)).
Proof.
  rewrite qstart_eq. cbn. rewrite HT, HC, !map_app. cbn [map fst]. rewrite app_nil_r. rewrite <- ?app_assoc. do 2 apply Permutation_app_head.
  change (qb_addr b :: map qb_addr r) with ([qb_addr b] ++ map qb_addr r). apply Permutation_app_comm.
Qed.
Lemma qstart_used : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st1 c).
Proof.
  intros c Hc. rewrite !used_cptrs_eq.
  replace (avail_cptrs st1 c) with (avail_cptrs st c) by (rewrite qstart_eq; reflexivity).
  replace (live_cptrs st1 c) with (live_cptrs st c) by (rewrite qstart_eq; reflexivity).
  replace (rbeg st1 24) with (rbeg st 24) by (rewrite qstart_eq; reflexivity).
  replace (st_qpend st1) with (st_qpend st) by (rewrite qstart_eq; reflexivity).
  replace (st_apend st1) with (st_apend st) by (rewrite qstart_eq; reflexivity).
  replace (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)) by (rewrite qstart_eq; reflexivity).
  do 2 apply Permutation_app_head. apply Permutation_app; [apply Permutation_map; apply Permutation_filter'; apply Permutation_sym; exact qstart_qelems|].
  apply Permutation_app_head. apply Permutation_app_tail.
  destruct (c =? 24); [| apply Permutation_refl]. apply Permutation_map. apply Permutation_sym. exact qstart_qall.
Qed.
Theorem RTWFq_qstart : RTWFq st1.
Proof.
  rewrite qstart_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _).
  unfold qall in Q1. cbn [st_qthread st_qglobal st_qtmp st_qcur st] in Q1. rewrite HT, HC in Q1.
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. rewrite <- qstart_eq. apply qstart_used. exact Hc.
  - cbn [app]. rewrite !all_blocks_eq. rewrite <- qstart_eq.
    replace (st_lb st1) with (st_lb st) by (rewrite qstart_eq; reflexivity). replace (st_qpend st1) with (st_qpend st) by (rewrite qstart_eq; reflexivity).
    apply Permutation_app_head. apply Permutation_app_tail. apply Permutation_sym. exact qstart_qelems.
  - constructor.
  - intros b' Hb'. rewrite qall_q_set in Hb'. apply Q1. rewrite !in_app_iff. cbn [In map fst].
    apply in_app_iff in Hb' as [Hb'|Hb']; [tauto|]. apply in_app_iff in Hb' as [Hb'|Hb']; [tauto|].
    apply in_app_iff in Hb' as [Hb'|Hb']; [tauto|]. cbn [map fst In] in Hb'. tauto.
  - exact Q2.
  - intros bd [<-|[]]. cbn [fst snd]. unfold qb_count. lia.
  - exact Q4.
  - cbn [st_qglobal st_qtmp st_qcur st] in Q5. rewrite HT, HC in Q5. cbn [map fst] in *. rewrite !qc_bytes_cons in *. rewrite qc_bytes_nil in *. lia.
  - exact Q6.
Qed.
Theorem rt_prov_qstart : rt_prov st1 = rt_prov st.
Proof.
  rewrite qstart_eq. rewrite (rt_prov_q_set st _ _ _ _ _ _).
  2:{ rewrite <- qstart_eq. replace (st_qpend st) with QP by reflexivity. apply Permutation_app_tail. apply Permutation_sym. exact qstart_qelems. }
  unfold prov_nb, prov_q, thread_room. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). cbn [st_qthread st]. lia.
Qed.
End QSTART.

(* [comment removed for export] *)
Section QCHUNK.
Variables (b : qbatch) (d A n : Z).
Hypothesis HC : b5 = [(b, d)].
Hypothesis HD : 0 <= d < qb_count b.
Hypothesis HE : nthz (qb_elems b) d (0, 0) = (A, n).
Hypothesis HP : bprim n = true.
Hypothesis HAPE : AP = [].
Let c := pclass n.
Let k := b_cptr st A n.
Let st1 := st_qchunk st c k.
Lemma qchunk_eq : st1 = q_set st a10 a11 ((c, k) :: AP) QP b4 [(b, d + 1)].
Proof. subst st1. unfold st_qchunk. cbn [st_qcur st]. rewrite HC. reflexivity. Qed.

Lemma skipn_nth : forall {X} (m : nat) (l : list X) dflt, (m < length l)%nat -> skipn m l = nth m l dflt :: skipn (S m) l.
Proof.
  intros X m. induction m as [|m IH]; intros [|x l] dflt Hm; cbn in Hm |- *; try lia; [reflexivity|].
  apply IH. lia.
Qed.
Lemma skipn_d : skipn (Z.to_nat d) (qb_elems b) = (A, n) :: skipn (Z.to_nat (d + 1)) (qb_elems b).
Proof.
  unfold qb_count in HD. rewrite <- HE. unfold nthz. replace (d <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Z2Nat.inj_add, Nat.add_1_r by lia. apply skipn_nth. lia.
Qed.

Lemma qchunk_qelems : Permutation (qelems st) ((A, n) :: qelems st1).
Proof.
  rewrite qchunk_eq. cbn -[skipn Z.to_nat]. rewrite HC. cbn [flat_map fst snd]. rewrite !app_nil_r, skipn_d. apply Permutation_sym. apply Permutation_middle.
Qed.
Lemma qchunk_qall : map qb_addr (qall st1) = map qb_addr (qall st).
Proof. rewrite qchunk_eq. cbn. rewrite HC. reflexivity. Qed.
Lemma qchunk_k_range : 1 <= c <= 30.
Proof. exact (proj1 (prim_facts n HP)). Qed.

Lemma qchunk_used : forall c', 0 <= c' < KNUMCLASSES -> Permutation (used_cptrs st c') (used_cptrs st1 c').
Proof.
  intros c' Hc'. rewrite !used_cptrs_eq.
  replace (avail_cptrs st1 c') with (avail_cptrs st c') by (rewrite qchunk_eq; reflexivity).
  replace (live_cptrs st1 c') with (live_cptrs st c') by (rewrite qchunk_eq; reflexivity).
  replace (rbeg st1 24) with (rbeg st 24) by (rewrite qchunk_eq; reflexivity).
  replace (st_qpend st1) with (st_qpend st) by (rewrite qchunk_eq; reflexivity).
  replace (st_apend st1) with ((c, k) :: AP) by (rewrite qchunk_eq; reflexivity). change (st_apend st) with AP.
  replace (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)) by (rewrite qchunk_eq; reflexivity).
  set (h := fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)).
  rewrite qchunk_qall. do 2 apply Permutation_app_head.
  (* [comment removed for export] *)
  assert (EQ : Permutation (map h (List.filter (cf c') (qelems st))) (map h (List.filter (cf c') ((A, n) :: qelems st1)))).
  { apply Permutation_map. apply Permutation_filter'. exact qchunk_qelems. }
  cbn [List.filter] in EQ. unfold cf in EQ at 2. cbn [fst snd] in EQ. rewrite HP in EQ. cbn [andb] in EQ. fold c in EQ.
  cbn [List.filter fst]. destruct (Z.eqb_spec c c') as [<-|NE].
  - rewrite ?Z.eqb_refl in EQ. cbn [map] in EQ. change (h (A, n)) with k in EQ. cbn [map snd].
    lazymatch goal with |- Permutation (?Q ++ ?P ++ ?B ++ ?Ap) (?Q1 ++ ?P1 ++ ?B1 ++ k :: ?Ap1) =>
      apply (Permutation_trans (l' := (k :: Q1) ++ P ++ B ++ Ap)); [apply Permutation_app_tail; exact EQ|] end.
    cbn [app]. rewrite !app_assoc. apply Permutation_middle.
  - replace (c =? c') with false in EQ by (symmetry; apply Z.eqb_neq; exact NE). apply Permutation_app_tail. exact EQ.
Qed.

Theorem RTWFq_qchunk : RTWFq st1.
Proof.
  rewrite qchunk_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _). pose proof qchunk_k_range as CR.
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := [(A, n)]).
  - intros c' Hc'. rewrite <- qchunk_eq. apply qchunk_used. exact Hc'.
  - rewrite !all_blocks_eq. rewrite <- qchunk_eq.
    replace (st_lb st1) with (st_lb st) by (rewrite qchunk_eq; reflexivity). replace (st_qpend st1) with (st_qpend st) by (rewrite qchunk_eq; reflexivity).
    apply Permutation_trans with (st_lb st ++ ((A, n) :: qelems st1) ++ st_qpend st).
    + apply Permutation_app_head. apply Permutation_app_tail. exact qchunk_qelems.
    + cbn [app]. apply Permutation_sym. apply Permutation_middle.
  - constructor; [exact HP| constructor].
  - intros b' Hb'. apply Q1. unfold qall. cbn [st_qthread st_qglobal st_qtmp st_qcur st]. rewrite HC. rewrite qall_q_set in Hb'. exact Hb'.
  - exact Q2.
  - intros bd [<-|[]]. cbn [fst snd]. lia.
  - intros ck [<-|Hck]; [cbn [fst]; unfold KNUMCLASSES; lia| exact (Q4 ck Hck)].
  - cbn [st_qglobal st_qtmp st_qcur st] in Q5. rewrite HC in Q5. cbn [map fst] in *. exact Q5.
  - destruct Q6 as [I1 I2]. cbn [st_apend st_qpend st] in I1, I2. rewrite HAPE. rewrite zlen_cons, zlen_nil. split; [lia| exact I2].
Qed.
Theorem rt_prov_qchunk : rt_prov st1 = rt_prov st.
Proof.
  rewrite qchunk_eq. rewrite (rt_prov_q_set_gone st _ _ _ _ _ _ [(A, n)]).
  2:{ rewrite <- qchunk_eq. replace (st_qpend st) with QP by reflexivity. cbn [app]. change ((A, n) :: qelems st1 ++ QP) with (((A, n) :: qelems st1) ++ QP).
      apply Permutation_app_tail. exact qchunk_qelems. }
  unfold prov_nb, prov_q, thread_room. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). cbn [st_qthread st map zsum fold_right snd].
  unfold rp. rewrite HP. unfold zsum. cbn [fold_right]. lia.
Qed.
End QCHUNK.

(* [comment removed for export] *)
Section QBATCH.
Variables (b : qbatch) (kb : Z).
Hypothesis HC : b5 = [(b, qb_count b)].
Hypothesis HK : qb_addr b = cptr_addr st 24 kb.
Hypothesis HAPE : AP = [].
Let st1 := st_qbatch st kb.
Lemma qbatch_eq : st1 = q_set st a10 a11 ((24, kb) :: AP) QP b4 []. Proof. reflexivity. Qed.
Lemma skipn_all : forall {X} (l : list X), skipn (length l) l = [].
Proof. intros X l. induction l; [reflexivity| cbn; assumption]. Qed.
Lemma qbatch_qelems : qelems st1 = qelems st.
Proof.
  rewrite qbatch_eq. cbn -[skipn Z.to_nat]. rewrite HC. cbn [flat_map fst snd]. unfold qb_count. rewrite Nat2Z.id, skipn_all. rewrite !app_nil_r. reflexivity.
Qed.
Lemma qbatch_qall : Permutation (qb_addr b :: map qb_addr (qall st1)) (map qb_addr (qall st)).
Proof.
  rewrite qbatch_eq. cbn. rewrite HC, !map_app. cbn [map fst]. rewrite app_nil_r. rewrite !app_assoc. apply Permutation_cons_append.
Qed.
Lemma qbatch_used : forall c, 0 <= c < KNUMCLASSES -> Permutation (used_cptrs st c) (used_cptrs st1 c).
Proof.
  intros c Hc. rewrite !used_cptrs_eq.
  replace (avail_cptrs st1 c) with (avail_cptrs st c) by (rewrite qbatch_eq; reflexivity).
  replace (live_cptrs st1 c) with (live_cptrs st c) by (rewrite qbatch_eq; reflexivity).
  replace (rbeg st1 24) with (rbeg st 24) by (rewrite qbatch_eq; reflexivity).
  replace (st_qpend st1) with (st_qpend st) by (rewrite qbatch_eq; reflexivity).
  replace (st_apend st1) with ((24, kb) :: AP) by (rewrite qbatch_eq; reflexivity). change (st_apend st) with AP.
  replace (fun b0 : Z * Z => b_cptr st1 (fst b0) (snd b0)) with (fun b0 : Z * Z => b_cptr st (fst b0) (snd b0)) by (rewrite qbatch_eq; reflexivity).
  rewrite qbatch_qelems. do 4 apply Permutation_app_head.
  cbn [List.filter fst]. destruct (Z.eqb_spec 24 c) as [<-|NE].
  - cbn [Z.eqb Pos.eqb map snd].
    apply Permutation_trans with ((kb :: map (fun a : Z => (a - rbeg st 24) / 16) (map qb_addr (qall st1))) ++ map snd (List.filter (fun ck : Z * Z => fst ck =? 24) AP)).
    + apply Permutation_app_tail. replace kb with ((qb_addr b - rbeg st 24) / 16) by (rewrite HK; unfold cptr_addr; Z.div_mod_to_equations; lia).
      change ((qb_addr b - rbeg st 24) / 16 :: map (fun a : Z => (a - rbeg st 24) / 16) (map qb_addr (qall st1)))
        with (map (fun a : Z => (a - rbeg st 24) / 16) (qb_addr b :: map qb_addr (qall st1))).
      apply Permutation_map. apply Permutation_sym. exact qbatch_qall.
    + cbn [app]. apply Permutation_middle.
  - replace (c =? 24) with false by (symmetry; apply Z.eqb_neq; lia). apply Permutation_refl.
Qed.
Theorem RTWFq_qbatch : RTWFq st1.
Proof.
  rewrite qbatch_eq. pose proof WF as (_ & WC & _ & _ & (Q1 & Q2 & Q5 & Q6 & Q3 & Q4) & _).
  eapply (RTWFq_qstep st _ _ _ _ _ _ WF) with (gone := []).
  - intros c Hc. rewrite <- qbatch_eq. apply qbatch_used. exact Hc.
  - cbn [app]. rewrite !all_blocks_eq. rewrite <- qbatch_eq, qbatch_qelems.
    replace (st_lb st1) with (st_lb st) by (rewrite qbatch_eq; reflexivity). replace (st_qpend st1) with (st_qpend st) by (rewrite qbatch_eq; reflexivity).
    apply Permutation_refl.
  - constructor.
  - intros b' Hb'. apply Q1. unfold qall. cbn [st_qthread st_qglobal st_qtmp st_qcur st]. rewrite HC. rewrite qall_q_set in Hb'. cbn [map fst] in *.
    rewrite app_nil_r in Hb'. rewrite !in_app_iff in Hb'. rewrite !in_app_iff. cbn [In]. tauto.
  - exact Q2.
  - intros bd [].
  - intros ck [<-|Hck]; [cbn [fst]; unfold KNUMCLASSES; lia| exact (Q4 ck Hck)].
  - cbn [st_qglobal st_qtmp st_qcur st] in Q5. rewrite HC in Q5. cbn [map fst] in *. rewrite qc_bytes_cons, qc_bytes_nil in Q5. rewrite qc_bytes_nil.
    pose proof (qc_bytes_nonneg [b]) as BP. rewrite qc_bytes_cons, qc_bytes_nil in BP. lia.
  - destruct Q6 as [I1 I2]. cbn [st_apend st_qpend st] in I1, I2. rewrite HAPE. rewrite zlen_cons, zlen_nil. split; [lia| exact I2].
Qed.
Theorem rt_prov_qbatch : rt_prov st1 = rt_prov st.
Proof.
  rewrite qbatch_eq. rewrite (rt_prov_q_set st _ _ _ _ _ _).
  2:{ rewrite <- qbatch_eq, qbatch_qelems. apply Permutation_refl. }
  unfold prov_nb, prov_q, thread_room. rewrite (proj1 (q_set_fields st _ _ _ _ _ _)). cbn [st_qthread st]. lia.
Qed.
End QBATCH.
End QI.


End CeilWrap.
End RTW_q_wf.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep RT_kit CJ_iface RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_fp RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_primary_iface RTW_quarantine_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RT_trans.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_pop.
Import RTW_m_c1.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_sec_dstateP.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_sec_dstateP.RTW_q_trans.
Import RTW_q_wf.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RTWFq_enq_last' : forall st q b A n, RTWFq st -> st_qthread st = q ++ [b] -> In (A, n) (st_qpend st) ->
  qb_count b < QBATCH_CAP -> 0 <= n -> RTWFq (st_enq_last st A n).
Proof. intros st q b A n WF HQ HIN ROOM Hn. destruct st. eapply RTWFq_enq_last; eauto. Qed.
Lemma rt_prov_enq_last' : forall st q b A n, RTWFq st -> st_qthread st = q ++ [b] -> In (A, n) (st_qpend st) ->
  qb_count b < QBATCH_CAP -> 0 <= n -> rt_prov (st_enq_last st A n) <= rt_prov st + fp n.
Proof. intros st q b A n WF HQ HIN ROOM Hn. destruct st. eapply rt_prov_enq_last; eauto. Qed.
Lemma RTMODEL_enq_last' : forall st A n mo, RTMODEL st mo -> RTMODEL (st_enq_last st A n) mo.
Proof. intros. unfold st_enq_last. apply RTMODEL_q_set. assumption. Qed.
Lemma GWIN_enq_last' : forall st A n m mo g, GWIN st m mo g -> GWIN (st_enq_last st A n) m mo g.
Proof. intros. unfold st_enq_last. apply GWIN_q_set. assumption. Qed.
Lemma SWIN_enq_last' : forall st A n g, SWIN st g -> SWIN (st_enq_last st A n) g.
Proof. intros. unfold st_enq_last. apply SWIN_q_set. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma RTWFq_enq_new' : forall st k A n, RTWFq st -> In (A, n) (st_qpend st) -> In (24, k) (st_apend st) -> 0 <= n ->
  RTWFq (st_enq_new st k A n).
Proof. intros st k A n WF HIN HK Hn. destruct st. eapply RTWFq_enq_new; eauto. Qed.
Lemma rt_prov_enq_new' : forall st k A n, RTWFq st -> In (A, n) (st_qpend st) -> In (24, k) (st_apend st) -> 0 <= n ->
  (st_qthread st = [] \/ thread_room st = 0) ->
  rt_prov (st_enq_new st k A n) + 2 * csize 24 <= rt_prov st + fp n.
Proof. intros st k A n WF HIN HK Hn FULL. destruct st. eapply rt_prov_enq_new; eauto. Qed.
Lemma RTMODEL_enq_new' : forall st k A n mo, RTMODEL st mo -> RTMODEL (st_enq_new st k A n) mo.
Proof. intros. unfold st_enq_new. apply RTMODEL_q_set. assumption. Qed.
Lemma GWIN_enq_new' : forall st k A n m mo g, GWIN st m mo g -> GWIN (st_enq_new st k A n) m mo g.
Proof. intros. unfold st_enq_new. apply GWIN_q_set. assumption. Qed.
Lemma SWIN_enq_new' : forall st k A n g, SWIN st g -> SWIN (st_enq_new st k A n) g.
Proof. intros. unfold st_enq_new. apply SWIN_q_set. assumption. Qed.

(* [comment removed for export] *)
Lemma thread_room_full : forall st q l, st_qthread st = q ++ [l] -> qb_count l = QBATCH_CAP -> thread_room st = 0.
Proof.
  intros st q l HQ HF. unfold thread_room. rewrite HQ. destruct (q ++ [l]) eqn:E; [destruct q; discriminate|]. rewrite <- E, last_last. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition enq_rel (st st' : rtstate) (A n : Z) : Prop :=
  same_but_quarantine st st'
  /\ st_qpend st' = remove_first ck_eqb (A, n) (st_qpend st)
  /\ st_qglobal st' = st_qglobal st /\ st_qtmp st' = st_qtmp st /\ st_qcur st' = st_qcur st
  /\ st_qthread st' <> []
  /\ qc_bytes (st_qthread st') <= qc_bytes (st_qthread st) + usz n + QBATCH_SIZE
  /\ (forall c, 0 <= c < KNUMCLASSES -> c <> 24 -> fresh_cls st c -> fresh_cls st' c).

Lemma enq_rel_last : forall st q b A n, st_qthread st = q ++ [b] -> enq_rel st (st_enq_last st A n) A n.
Proof.
  intros st q b A n HQ. unfold enq_rel, same_but_quarantine, st_enq_last.
  pose proof (q_set_same st (upd_last (st_qthread st) (fun b0 => qb_push b0 (A, n))) (st_qglobal st) (st_apend st)
                 (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st)) as SM. cbn zeta in SM.
  destruct SM as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22).
  destruct (q_set_fields st (upd_last (st_qthread st) (fun b0 => qb_push b0 (A, n))) (st_qglobal st) (st_apend st)
                 (remove_first ck_eqb (A, n) (st_qpend st)) (st_qtmp st) (st_qcur st)) as (F1 & F2 & F3 & F4 & F5 & F6).
  rewrite E1, E2, E3, E7, E10, E11, E12, E13, E14, E15, E16, E17, E20, E21, E22, F1, F2, F3, F4, F5, F6.
  split; [repeat (split; [first [reflexivity| apply dtls_same_of_eq; exact E18| exists []; rewrite E19; symmetry; apply app_nil_r]|]); reflexivity|].
  repeat (split; [reflexivity|]).
  rewrite HQ, upd_last_snoc. split; [destruct q; discriminate|].
  split.
  - rewrite !qc_bytes_app, !qc_bytes_cons, !qc_bytes_nil, qb_size_push. unfold usz, QBATCH_SIZE. lia.
  - intros c Hc NE FR. apply q_set_fresh. exact FR.
Qed.

Lemma enq_rel_new : forall st st2 pre k A n, refill_rel st st2 24 1 \/ st2 = st -> st_apend st = [] -> cch st2 24 = pre ++ [k] ->
  enq_rel st (st_enq_new (st_pop st2 24 k pre) k A n) A n.
Proof.
  intros st st2 pre k A n RR HAP HC.
  assert (SB : same_but_primary st st2 /\ st_apend st2 = st_apend st /\ (forall c, 0 <= c < KNUMCLASSES -> c <> 24 -> rg st2 c = rg st c /\ cch st2 c = cch st c)).
  { destruct RR as [(P1 & P2 & P3 & P4 & P5)| ->].
    - split; [exact P1|]. split; [exact P2| exact P4].
    - split; [| split; [reflexivity| intros; split; reflexivity]].
      unfold same_but_primary. repeat (split; [first [reflexivity| apply dtls_same_refl| apply loose0_ext_refl]|]). reflexivity. }
  destruct SB as (P & AP2 & OTH).
  destruct P as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14 & P15 & P16 & P17 & P18 & P19 & P20 & P21 & P22 & P23 & P24).
  set (st1 := st_pop st2 24 k pre).
  pose proof (st_pop_same st2 24 k pre) as SP'. fold st1 in SP'.
  destruct SP' as (S1 & S2 & S3 & S4 & S5 & S6 & S7 & S8 & S9 & S10 & S11 & S12 & S13 & S14 & S15 & S16 & S17 & S18 & S19 & S20 & S21 & S22 & S23 & S24 & S25 & S26 & S27 & S28).
  unfold enq_rel, same_but_quarantine, st_enq_new.
  pose proof (q_set_same st1 (st_qthread st1 ++ [mkQB (cptr_addr st1 24 k) [(A, n)]]) (st_qglobal st1) (remove_first ck_eqb (24, k) (st_apend st1))
                 (remove_first ck_eqb (A, n) (st_qpend st1)) (st_qtmp st1) (st_qcur st1)) as SM. cbn zeta in SM.
  destruct SM as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11 & E12 & E13 & E14 & E15 & E16 & E17 & E18 & E19 & E20 & E21 & E22).
  destruct (q_set_fields st1 (st_qthread st1 ++ [mkQB (cptr_addr st1 24 k) [(A, n)]]) (st_qglobal st1) (remove_first ck_eqb (24, k) (st_apend st1))
                 (remove_first ck_eqb (A, n) (st_qpend st1)) (st_qtmp st1) (st_qcur st1)) as (F1 & F2 & F3 & F4 & F5 & F6).
  unfold dtls_same, loose0_ext in *.
  rewrite ?E1, ?E2, ?E3, ?E7, ?E10, ?E11, ?E12, ?E13, ?E14, ?E15, ?E16, ?E17, ?E18, ?E19, ?E20, ?E21, ?E22, ?F1, ?F2, ?F3, ?F4, ?F5, ?F6.
  rewrite ?S1, ?S2, ?S3, ?S4, ?S5, ?S6, ?S8, ?S9, ?S10, ?S11, ?S12, ?S13, ?S14, ?S15, ?S16, ?S17, ?S18, ?S19, ?S20, ?S24, ?S25, ?S26, ?S27.
  rewrite ?P1, ?P2, ?P3, ?P4, ?P7, ?P8, ?P9, ?P10, ?P11, ?P12, ?P13, ?P14, ?P15, ?P16, ?P19, ?P20, ?P21, ?P22, ?P23, ?P24, ?AP2, ?HAP.
  destruct P17 as [P17a P17b].
  split.
  { repeat (split; [first [reflexivity| (split; [exact P17a| exact P17b])| exact P18| (cbn; rewrite ?Z.eqb_refl; reflexivity)]|]). reflexivity. }
  split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
  split; [destruct (st_qthread st); discriminate|].
  split.
  - rewrite qc_bytes_app, qc_bytes_cons, qc_bytes_nil, qb_size_one. unfold usz. lia.
  - intros c Hc NE FR. apply q_set_fresh. unfold fresh_cls in *. destruct (OTH c Hc NE) as [R1 R2].
    unfold rg, cch in *. fold st1. rewrite S22, S28. rewrite nthz_updz_other by lia. rewrite R1, R2. exact FR.
Qed.


End CeilWrap.
