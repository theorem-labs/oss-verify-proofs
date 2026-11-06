(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz ARtSf1m ARtSnjd ARtSrgm AMTac ARt2_lib ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeS.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt4z85 ARt4dju ANodeA7 ANodeA6 ANodl61 ANodijx ANod9v0 AFreeH AFreeH0 AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeR.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeS AFreeR.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSf1m OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSnjd OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSrgm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR.ARt4ak4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeS.ARt4tam OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt4z85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt4dju OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodijx OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANod9v0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeC OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR.AFreeC2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeS OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR.

Module AFreeC3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr Frame Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yd Require Import DA_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo Asan12c Asanqj4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import SysStep.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface AState AInv AIcpm9j AIcp0e6 ARtStmts ARtSscs ARtS4t2 ARtSoqz AMTac ARt2_lib ARt_u2d.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpm9j.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require ARt3o73 ARt_png ARt_fpo ANodeA7 ANodeA6 ANodl61 AFreeH AFreeH0.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AState OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AInv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtStmts OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSscs OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtS4t2 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARtSoqz OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AMTac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt2_lib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_u2d OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j.AFreeLib OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt3o73 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_png OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ARt_fpo OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodeA6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ANodl61 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeH0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require Import AFreeC.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= tryif OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_goal_has_var then (Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker) else first [ solve [OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.PropExec.noncert_clear_all; Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker] | Stdlib.micromega.Zify.zify; xlia Stdlib.micromega.Lia.zchecker ].
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.

Section CachePush3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  Variables (lo C c sb ri k maxc nf mfa : Z) (ks : list word) (statv nfs v88 : word).

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp).
  #[warnings="-notation-for-abbreviation"] Local Notation E := (C + 80 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation R := (ri + 128 * c).
  #[warnings="-notation-for-abbreviation"] Local Notation fa := (free_array_of sb c).
  #[warnings="-notation-for-abbreviation"] Local Notation h := (Z.shiftr maxc 1).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo usp.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis SPA : usp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  (* [comment removed for export] *)
  Hypothesis CLO : aobj C 3888.   (* [comment removed for export] *)
  Hypothesis CHI : C + 3888 <= alloc_ceiling.
  Hypothesis CAL : C mod 16 = 0.
  Hypothesis CR : 1 <= c <= 30.
  Hypothesis KR : 0 <= k < 2^28.
  (* [comment removed for export] *)
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_cs : apart C 3888 sb (2^37).
  Hypothesis SEP_cr : apart C 3888 ri 4096.
  (* [comment removed for export] *)
  Hypothesis MXR : 2 <= maxc <= 16.
  Hypothesis MXE : maxc mod 2 = 0.
  Hypothesis LKS : length ks = 16%nat.
  Hypothesis NF0 : 0 <= nf.
  Hypothesis NFH : nf + h < 2^27.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1d78 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m 0xb1d88 [C8 (wz ri)].
  Hypothesis CITV : ro_cells rsegs m 0xb1d80 [C4 (wz 4294967295)].
  Hypothesis CGPS : ro_cells rsegs m 0xa9170 [C8 (wz 0x144e60)].
  Hypothesis CPS : ro_cells rsegs m 0x144e60 [C8 (wz 4096)].
  (* [comment removed for export] *)
  Hypothesis PC : rw_cells rsegs m E [C4 (wz maxc); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)].
  Hypothesis STA : rw_cells rsegs m (C + 2576) [C8 statv].
  Hypothesis MX : rw_cells rsegs m R [C8 (wz 0)].
  Hypothesis NFC : rw_cells rsegs m (R + 16) [C8 (wz nf)].
  Hypothesis MFA : rw_cells rsegs m (R + 24) [C8 (wz mfa)].
  Hypothesis NFS : rw_cells rsegs m (R + 80) [C8 nfs; C8 v88].


  Definition cpush_drain_fast_post : machine_state -> Prop := fun ms' =>
    exists (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' statv' : word) (m' : word -> option byte),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom rsegs)
    /\ munch (cpush_drain_W sp 320 C c ri sb nf h) m m'
    /\ wmono rsegs m m' /\ mem_inv rsegs m' /\ stk rsegs m' lo usp
    /\ rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz k)))]
    /\ rw_cells rsegs m' (C + 2576) [C8 statv']
    /\ rw_cells rsegs m' R [C8 (wz 0)]
    /\ rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))]
    /\ rw_cells rsegs m' (R + 24) [C8 (wz mfa)]
    /\ rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88]
    /\ u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)).

  Hypothesis CPMH : ro_cells rsegs m 0xb1d90 [C1 (Z_to_bv 8 0)].
  Hypothesis CGCF : ro_cells rsegs m 0xa9180 [C8 (wz CF)].
  Hypothesis CDMP : ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)].
  Hypothesis MFA0 : 0 <= mfa.
  Hypothesis MFAM : mfa mod kFaMap = 0.
  #[warnings="-notation-for-abbreviation"] Local Notation nm := (round_up (4 * (nf + h)) kFaMap).
  #[warnings="-notation-for-abbreviation"] Local Notation fe := (sb + c * 4294967296 + kFreeArrayOffset + mfa).

  (* [comment removed for export] *)
  Lemma cpush_drain_map_pre2 : forall (Q : machine_state -> Prop),
    lo <= usp - 688 -> mfa < 4 * (nf + h) ->   (* [comment removed for export] *)
    (forall (t0' t1' t2' a6' t3' t4' t5' t6' : word) (scr scr2 scr3 scr4 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (usp + -48) (lcd_frame s4 s3 s2 s1 s0 ra) ->
        rw_cells rsegs m' (usp + -48 + -64) (lcdrain_frame scr (wz lcdealloc_after)) ->
        rw_cells rsegs m' (usp + -48 + -64 + -128)
                 (rta_frame scr2 (R + 8) s11 s10 s9 s8 s7 s6 s5 (wz (sb + c * 4294967296 + 16 * k)) (wz c) (wz 0xb1d58) (wz C) (wz E) (wz lcdrain_ret)) ->
        rw_cells rsegs m' (usp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (usp + -48 + -56)) (wz c) (wz nf) (wz R) (wz rta_efasret)) ->
        rw_cells rsegs m' (usp + -48 + -64 + -128 + -48 + -128)
                 (mapcb_frame scr4 (wz 0xb1d58) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) ->   (* [comment removed for export] *)
        rw_cells rsegs m' E [C4 (wz (maxc - h)); C4 (wz maxc); C8 (wz (class_size c)); CB 64 (u32s ks)] ->
        rw_cells rsegs m' (C + 2576) [C8 statv] ->
        rw_cells rsegs m' R [C8 (wz kMutexWriter)] ->
        rw_cells rsegs m' (R + 16) [C8 (wz nf)] ->
        rw_cells rsegs m' (R + 24) [C8 (wz mfa)] ->
        rw_cells rsegs m' (R + 80) [C8 nfs; C8 v88] ->
        munch [(usp - 688, usp); (E, E + 4); (R, R + 8)] m m' -> wmono rsegs m m' -> mem_inv rsegs m' ->
        stk rsegs m' lo (usp + -48 + -64 + -128 + -48 + -128) ->
        Q (MSsvc (mkR (wz mapfixed_resume) (wz (usp + -48 + -64 + -128 + -48 + -128)) gp tp t0' t1' t2' (wz (nm - mfa)) (wz 1)
                      (wz fe) (wz (nm - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6' (wz 222)
                      (wz fe) (wz efas_name) (wz PSC) (wz h) (wz (E + 16 + 4 * (maxc - h))) (wz (nf + h)) (wz 2305843009213693952)
                      (wz fa) (wz 1152921504607895551) (wz kMutexWriter) t3' t4' t5' t6')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz C) (wz 0xb1d58) (wz c) (wz (sb + c * 4294967296 + 16 * k)) a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz lcdealloc_entry) fc None m (seg_rom rsegs)).
  Proof.
    intros Q LOLE NOFIT K.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (maxc_half maxc MXR MXE) as [MH HR8]. pose proof (class_size_range c CR) as CSR. unfold kMaxSize in CSR.
    unfold kHighMemBeg, free_array_of, kFaMap, CF in *.
    pose proof (munch_refl [(usp - 688, usp); (E, E + 4); (R, R + 8)] m) as MU.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    eapply (lcdealloc_full_ok _ _ gp tp t0 t1 t2 s0 s1 _ _ _ _ a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
              lo C c (sb + c * 4294967296 + 16 * k) maxc ks); [> try (fside CV) .. | idtac].
    intros a4b a5b m1 LF PC1 MU1 WM1 MI1 ST1. rewrite ?unsigned_lit in LF, MU1, ST1 by lia.
    clear PC. kpost MU1 WM1.
    unfold lcdealloc_after, lcdrain_entry.
    (* [comment removed for export] *)
    eapply (lcdrain_pre_ok _ _ gp tp t0 t1 t2 _ _ _ _ a6 a7 _ _ _ s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m1
              lo C E c maxc maxc (class_size c) ks); [> try (fside CV) .. | idtac].
    intros a6c scr m2 DF PC2 MU2 WM2 MI2 ST2. rewrite ?unsigned_lit in DF, MU2, ST2 by lia.
    clear PC1. kpost MU2 WM2.
    unfold lcdrain_ret, rta_entry. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply (rta_lock_ok _ _ gp tp t0 t1 t2 _ _ _ _ _ _ _ a6c a7 _ _ _ s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m2
              lo ri sb c (usp + -48 + -56) (C + 2560) (E + 16 + 4 * (maxc - h)) h nf); [> try (fside CV) .. | idtac].
    intros t0d t1d t2d a4d a5d a6d t3d t4d t5d t6d scr2 m3 MX3 NFC3 RF MU3 WM3 MI3 ST3.
    rewrite ?unsigned_lit in RF, MU3, ST3 by lia.
    clear MX NFC. kpost MU3 WM3.
    unfold rta_efasret, ARtSoqz.efas_entry. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    pose proof (roundup_famap_range (4 * (nf + h)) ltac:(lia)) as [NM1 NM2]. pose proof (roundup_famap_cap (4 * (nf + h)) ltac:(lia)) as NM3.
    eapply (efas_map_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3
              lo R (sb + c * 4294967296) (nf + h) mfa); [> try (fside CV) .. | idtac].
    all: try (unfold kFreeArrayOffset; lia).
    intros m4 scr3 EF MU4 WM4 MI4 ST4. rewrite ?unsigned_lit in EF, MU4, ST4 by lia.
    kpost MU4 WM4.
    unfold efas_mapret. rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    eapply (map_pre_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m4
              lo fe (nm - mfa) efas_name); [> try (fside CV) .. | idtac].
    all: try (unfold kFreeArrayOffset, efas_name, kFaMap, CF in *; first [lia | zmod]).
    intros t0e t1e t2e a6e t3e t4e t5e t6e scr4 m5 MF MU5 WM5 MI5 ST5. rewrite ?unsigned_lit in MF, MU5, ST5 by lia.
    kpost MU5 WM5. rewrite ?unsigned_lit by lia.
    unfold kFaMap, kFreeArrayOffset, efas_mapret, rta_efasret, lcdrain_ret, lcdealloc_after in K, MF |- *.
    eapply K.
    all: first [kcell | eassumption].
  Qed.
End CachePush3.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
End AFreeC3.

From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AFreeR2.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR3.AFreeC3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AFreeR2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tran6di.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8z6.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
Ltac2 hot_lia_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@CSR; @LOLE; @CEIL; @DR; @SBLO; @LKS; @MFA0; @PIN; @CR; @BLO; @RILO; @MXR; @SPR; @LBthr; @SEP_sr; @RIHI; @DSZ; @MHD; @HP; @FIT; @MUFA; @SZ16; @IR; @D16; @R8E; @NR; @CNTB; @SB16; @Bthr'; @BFORM; @KBR; @CV; @R82; @SEP_tr; @SBHI; @SPH; @X; @SEP_ts; @ISZ; @MHR; @SEP_tm; @K16; @IDX0; @R81; @RQ; @SEP_cs; @SEP_bp; @SEP_bt; @SEP_tp; @TR; @NF0; @NFH; @SEP_bm; @SEP_Cr; @TU; @Btp])).
Ltac hot_lia_full := OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8z6.dlia_nc.
Local Ltac lia ::= hot_lia_cut; hot_lia_full.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Dietcz7.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_cfree_lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Dietcz7.dl_tf_cfree_lia.
(* [comment removed for export] *)

Notation wz z := (Z_to_bv 64 z) (only parsing).

(* [comment removed for export] *)
Ltac slia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
  first [ exact I
        | lazymatch goal with
          | |- ?x + _ <= ?y \/ _ <= _ => apart_guided x y
          | |- ?x <= ?y \/ _ <= _ => apart_guided x y
          end
        | lia ].

(* [comment removed for export] *)
Local Ltac tf_region_find a n ::=
  let ba := tf_base a in
  match goal with
  | R : regn ?key ?B ?S |- _ => let bk := tf_base key in constr_eq ba bk; tf_with_region B S a n
  | R : regn_lit ?B ?S |- _ => tf_is_lit a; tf_with_region B S a n
  end.
Local Ltac tf_region_used segs m key ::=
  let bk := tf_base key in
  match goal with
  | H : rw_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : ro_cells segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : bytes_at segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  | H : stk segs m ?a _ |- _ => let ba := tf_base a in constr_eq ba bk
  end.
Local Ltac tf_apart B lo ::=
  let bB := tf_base B in let bl := tf_base lo in
  multimatch goal with
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq ba bB; constr_eq bc bl; eapply (apart_gl _ _ _ _ H)
  | H : apart ?a _ ?c _ |- _ => let ba := tf_base a in let bc := tf_base c in constr_eq bc bB; constr_eq ba bl; eapply (apart_gr _ _ _ _ H)
  end.
Local Ltac tf_same ::= first [ tf_cfree_lia | tf_lia ].
Local Ltac tf_regions ::=
  repeat match goal with K : aobjK ?X ?S |- _ => lazymatch goal with _ : regn X X S |- _ => fail | _ => pose proof (I : regn X X S) end end;
  try match goal with LO : alloc_ceiling <= ?lo /\ ?lo <= bv_unsigned ?sp - _ |- _ =>
        pose proof (I : regn (bv_unsigned sp) lo (bv_unsigned sp - lo)); pose proof (I : regn lo lo (bv_unsigned sp - lo)) end;
  try match goal with TSDL : ?L <= ?tsd /\ ?tsd + 8 <= _ |- _ => tf_closed L; pose proof (I : regn tsd 65536 6266880) end;
  pose proof (I : regn_lit 65536 6266880).
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; tf_transport segs m m' MU WM.
(* [comment removed for export] *)

(* [comment removed for export] *)
Local Ltac fside_asm := first
  [ lazymatch goal with
    | |- rw_cells ?s ?m ?a _ => match goal with H : rw_cells s m a _ |- _ => exact H end
    | |- ro_cells ?s ?m ?a _ => match goal with H : ro_cells s m a _ |- _ => exact H end
    end
  | eassumption ].
Local Ltac fside_tail E := lazymatch goal with |- ?g => tryif has_evar g then first [ fside_asm | eqrefl ]
             else first [ fside_asm | eqrefl | lia | unfold QINST, AINST; kung; lia | rewrite <- E; fside_asm
                        | match goal with S : sh _ = _ |- _ => rewrite S; fside_asm end | left; kung; lia
                        | rewrite ?unsigned_lit by lia; first [fside_asm | lia | kung; lia]
                        | kung; slia
                        | apply mod_add_lit; [lia | assumption | reflexivity]
                        | lazymatch goal with |- _ \/ _ => unfold boxed in *; kung; lia end ]
 end.
Local Ltac fside E ::=
  lazymatch goal with
  | |- apart _ _ _ _ => fail
  | |- forall _ : word, _ => fail
  | |- forall _ : machine_state, _ => fail
  | |- poison_consts _ => unfold poison_consts; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits; fside_asm
  | |- aobj _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else faobj end
  | |- aobjK _ _ => apply aobjK_i; faobj
  | |- pz_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else fpz end
  | |- pz0_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- fl_in _ _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- m2s_in _ => lazymatch goal with |- ?g => tryif has_evar g then try fside_asm else plia end
  | |- _ mod _ = _ => first [ zmod | fside_tail E ]
  | |- _ \/ _ => first [ solve [kung; slia] | fside_tail E ]
  | |- _ => fside_tail E
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@CR; @CEIL; @LOLE; @SBLO; @CSR; @IDX0; @SBHI; @Bctx'; @HP; @DR; @LBthr; @Bthr'; @MHD; @SZ16; @SB16; @D16; @MHR; @R8E; @RILO; @LBctx2])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TfIncl.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_with_region B S a n ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TfIncl.tf_with_region_fast B S a n.
(* [comment removed for export] *)
(* [comment removed for export] *)
Section DoRec3.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variables (gp tp t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 s11 t3 t4 t5 t6 : word) (rax sp : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte).
  (* [comment removed for export] *)
  Variables (lo T b cnt i : Z) (scr : list byte) (cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0 : word).
  (* [comment removed for export] *)
  Variables (tsd ctx thr sb ri : Z).

  Hypothesis CBPRIM : cbrec_prim2_stmt.

  #[warnings="-notation-for-abbreviation"] Local Notation usp := (bv_unsigned sp + 112).
  #[warnings="-notation-for-abbreviation"] Local Notation C := (thr + 208).

  Hypothesis MI : mem_inv rsegs m.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis SPH : usp <= 2^47.
  Hypothesis SPA : bv_unsigned sp mod 16 = 0.
  Hypothesis TPE : tp = wz TP.
  Hypothesis TC : thread_cells m tp tsd ctx thr.
  Hypothesis TSDL : 0x5e8328 <= tsd /\ tsd + 8 <= 0x60a000.
  Hypothesis PCo : poison_consts m.
  Hypothesis THRA : thr mod 16 = 0.
  (* [comment removed for export] *)
  Hypothesis BLO : kHighMemBeg <= b.
  Hypothesis BHI : b + 8192 <= alloc_ceiling.
  Hypothesis BAL : b mod 8 = 0.
  Hypothesis CNTB : 0 <= cnt <= 1021.
  (* [comment removed for export] *)
  Hypothesis SBLO : kHighMemBeg <= sb.
  Hypothesis SBHI : sb + 2^37 <= alloc_ceiling.
  Hypothesis SBAL : sb mod 4096 = 0.
  Hypothesis RILO : kHighMemBeg <= ri.
  Hypothesis RIHI : ri + 4096 <= alloc_ceiling.
  Hypothesis RIAL : ri mod 128 = 0.
  Hypothesis SEP_sr : sb + 2^37 <= ri.
  Hypothesis SEP_rs : apart ri 4096 sb (2^37).
  Hypothesis SEP_ts : apart thr 4096 sb (2^37).
  Hypothesis SEP_tr : apart thr 4096 ri 4096.
  Hypothesis SEP_tc : apart ctx 0x10000 thr 4096.
  Hypothesis SEP_cs : apart ctx 0x10000 sb (2^37).
  Hypothesis SEP_bt : apart b 8192 thr 4096.
  Hypothesis SEP_bc : apart b 8192 ctx 0x10000.
  Hypothesis SEP_br : apart b 8192 ri 4096.
  (* [comment removed for export] *)
  Hypothesis CSB : ro_cells rsegs m 0xb1d78 [C8 (wz sb)].
  Hypothesis CRI : ro_cells rsegs m RI_PTR [C8 (wz ri)].
  (* [comment removed for export] *)
  Hypothesis DF : rw_cells rsegs m (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0).
  Hypothesis TR : alloc_ceiling <= T.   (* [comment removed for export] *)
  Hypothesis TU : bv_unsigned sp + 112 <= T.
  (* [comment removed for export] *)
  Variable kb : Z.
  Hypothesis BFORM : b = sb + 24 * 2^32 + 16 * kb.
  Hypothesis KBR : 0 <= kb /\ 16 * kb + 8192 <= 3758096384.

  (* [comment removed for export] *)
  Lemma cbc_rw : forall (mm : word -> option byte),
    rw_cells rsegs mm (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs mm (bv_unsigned sp + 8) [C8 (wz C)].
  Proof.
    intros mm H. unfold dorec_frame in H.
    apply (rw_cells_app_split mm (bv_unsigned sp) [CB 8 scr] _) in H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
    apply (rw_cells_app_split mm _ [C8 (wz C)] _) in H as [H _]. exact H.
  Qed.
  Lemma cbc_ro : forall (mm : word -> option byte),
    rw_cells rsegs mm (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    ro_cells rsegs mm (bv_unsigned sp + 8) [C8 (wz C)].
  Proof.
    intros mm H. unfold dorec_frame in H.
    apply (rw_cells_app_split mm (bv_unsigned sp) [CB 8 scr] _) in H as [_ H]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in H.
    exact (rw_ro_prefix1 mm _ _ _ H).
  Qed.

  (* [comment removed for export] *)
  #[using="KBR BFORM kb DF CRI CSB SEP_bt SEP_cs SEP_tc SEP_tr SEP_ts SEP_sr RIAL RIHI RILO SBAL SBHI SBLO CNTB BAL BLO THRA PCo TSDL TC TPE SPA SPH CEIL ST MI CBPRIM ctx tsd Clg"] Lemma iter_prim_drainmap_pre2 : forall (Q : machine_state -> Prop)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' pw statv : word)
      (mh c idx d mu n b1 rf rfd maxc k nf mfa : Z) (old : list byte) (ks : list word) (nfs v88 : word),
    let nm := round_up (4 * (nf + Z.shiftr maxc 1)) kFaMap in let fe := sb + c * 4294967296 + kFreeArrayOffset + mfa in
    let D := C + 80 * c + 16 + 4 * (maxc - Z.shiftr maxc 1) in
    let size := class_size c in let p := sb + c * 2^32 + idx * size in let r8 := round_up n 8 in let E := C + 80 * c in
    let R := ri + 128 * c in let fa := free_array_of sb c in let h := Z.shiftr maxc 1 in
    lo <= bv_unsigned sp - 688 ->
    0 <= i < cnt -> bv_unsigned pw = mh -> mh = p + d -> 0 <= d < size -> d mod 16 = 0 -> 1 <= c <= 30 -> 0 <= idx -> (idx + 1) * size <= mu -> 0 <= mu < 2^32 ->
    16 * k = idx * size -> 1 <= n < 2^32 -> mh + 16 + r8 <= 2^47 -> 0 <= b1 < 256 -> 0 <= rf < 2^64 -> 0 <= rfd < 2^64 ->
    2 <= maxc <= 16 -> maxc mod 2 = 0 -> length ks = 16%nat -> 0 <= nf -> nf + h < 2^27 ->
    mfa < 4 * (nf + h) -> 0 <= mfa -> mfa mod kFaMap = 0 -> mu <= 3758096384 -> apart b 8192 p size ->
    ro_cells rsegs m 0xb1d80 [C4 (wz 4294967295)] ->
    ro_cells rsegs m 0xb1d90 [C1 (Z_to_bv 8 0)] -> ro_cells rsegs m 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m (b + 24 + 8 * i) [C8 pw] ->
    ro_cells rsegs m (ri + 128 * c + 48) [C8 (wz mu)] ->
    (d = 0 \/ rw_cells rsegs m p [C8 (wz kAllocBegMagic)]) ->
    rw_cells rsegs m mh [C1 (Z_to_bv 8 CHUNK_QUARANTINE); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    rw_cells rsegs m (sh (mh + 16)) [CB (Z.to_nat (r8 / 8)) old] ->
    rw_cells rsegs m (thr + 2840) [C8 (wz rf); C8 (wz rfd)] ->
    rw_cells rsegs m E [C4 (wz maxc); C4 (wz maxc); C8 (wz size); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m (R + 80) [C8 nfs; C8 v88] ->
    (forall (t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' : word) (lscr scr2 scr3 scr4 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        ro_cells rsegs m' (ri + 128 * c + 48) [C8 (wz mu)] ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        rw_cells rsegs m' (bv_unsigned sp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1d58) (wz T) (wz dorec_retpc)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64 + -128)
                 (rta_frame scr2 (R + 8) s11 s10 (wz (16 + i)) (wz (cnt + 16)) (wz (b + 152 + 8 * i)) (wz cnt) (wz (2^37)) (wz p) (wz c) (wz 0xb1d58) (wz C) (wz E) (wz lcdrain_ret)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (bv_unsigned sp + -48 + -56)) (wz c) (wz nf) (wz R) (wz rta_efasret)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)
                 (mapcb_frame scr4 (wz 0xb1d58) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) ->
        rw_cells rsegs m' E [C4 (wz (maxc - h)); C4 (wz maxc); C8 (wz size); CB 64 (u32s ks)] ->
        rw_cells rsegs m' (C + 2576) [C8 statv] ->
        rw_cells rsegs m' R [C8 (wz kMutexWriter)] -> rw_cells rsegs m' (R + 16) [C8 (wz nf)] -> rw_cells rsegs m' (R + 24) [C8 (wz mfa)] ->
        rw_cells rsegs m' (R + 80) [C8 nfs; C8 v88] ->
        munch [(bv_unsigned sp - 688, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (sh (mh + 16), sh (mh + 16) + r8 / 8);
               (thr + 2840, thr + 2856); (E, E + 4); (R, R + 8)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + -48 + -64 + -128 + -48 + -128) ->
        Q (MSsvc (mkR (wz mapfixed_resume) (wz (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)) gp tp t0'' t1'' t2'' (wz (nm - mfa)) (wz 1)
                      (wz fe) (wz (nm - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6'' (wz 222)
                      (wz fe) (wz efas_name) (wz PSC) (wz h) (wz D) (wz (nf + h)) (wz 2305843009213693952)
                      (wz fa) (wz 1152921504607895551) (wz kMutexWriter) t3'' t4'' t5'' t6'')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' i) F (wz dorec_callblk) fc None m (seg_rom rsegs)).
  Proof. try clear BHI. try clear SEP_rs. try clear SEP_bc. try clear SEP_br. try clear TR. try clear TU.   (* [comment removed for export] *)
    intros until v88. cbv zeta. intros LOLE IR PW MHD DR DAL CR IDX0 FIT MUR K16 NR MHR B1R RFR RFDR MXR MXE LKS NF0 NFH NOFIT MFA0 MFAM MUFA SEP_bp CITV CPMH CGCF CDMP
           ENT CMU MAG HDR SHC TRF LINE STA MX NFC MFA NFS K.
    pose proof (maxc_half maxc MXR MXE) as [MH HH8].
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (class_size_range c CR) as CSR. unfold kMaxSize in CSR. pose proof (class_size_mod32 c CR) as CSM.
    pose proof (round_up_ge n 8 ltac:(lia)) as R81. pose proof (round_up_lt n 8 ltac:(lia)) as R82. pose proof (round_up_mod n 8 ltac:(lia)) as R83.
    pose proof TPE as TPL. unfold TP in TPL. apply (f_equal bv_unsigned) in TPL. rewrite unsigned_lit in TPL by lia.
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold it_regs, kHighMemBeg, RI_PTR, LMA_L, LMA_STAT, CF in *. rewrite TPL in *. change (6194136 - 88) with 6194048 in Ctsd.
    pose proof (cbc_ro m DF) as CBC.
    remember (round_up n 8) as r8 eqn:HR8. remember (class_size c) as size eqn:HSZ.
    remember (sb + c * 2^32 + idx * size) as p eqn:HP.
    (* [comment removed for export] *)
    assert (SZ16 : size = 16 * (size / 16)).
    { pose proof (Z_div_mod_eq_full size 16) as X. rewrite (mod0_down size 32 16 ltac:(exists 2; reflexivity) CSM) in X. lia. }
    assert (SB16 : sb = 16 * (sb / 16)).
    { pose proof (Z_div_mod_eq_full sb 16) as X. rewrite (mod0_down sb 4096 16 ltac:(exists 256; reflexivity) SBAL) in X. lia. }
    assert (D16 : d = 16 * (d / 16)) by (pose proof (Z_div_mod_eq_full d 16) as X; rewrite DAL in X; lia).
    assert (R8E : r8 = 8 * (r8 / 8)) by (pose proof (Z_div_mod_eq_full r8 8) as X; rewrite R83 in X; lia).
    set (sq := size / 16) in *. set (bq := sb / 16) in *. set (dq := d / 16) in *. set (rq := r8 / 8) in *.
    assert (RQ : r8 / 8 = rq) by reflexivity. clearbody sq bq dq rq.
    assert (SHE : sh (mh + 16) = 2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880).
    { unfold sh, kShadowOffset. rewrite MHD, HP, SB16, SZ16, D16.
      replace (16 * bq + c * 2 ^ 32 + idx * (16 * sq) + 16 * dq + 16) with ((2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    rewrite SHE in *.
    (* [comment removed for export] *)
    assert (ISZ : 0 <= idx * size) by (apply Z.mul_nonneg_nonneg; lia).
    assert (PIN : sb <= p /\ p + size <= sb + 2^37) by (rewrite HP; lia).
    assert (DSZ : d + 16 <= size) by lia.
    assert (SEP_tp : apart thr 4096 p size) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_tm : apart thr 4096 mh 16) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cp : apart ctx 65536 p size) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cm : apart ctx 65536 mh 16) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_bm : apart b 8192 mh 16) by (revert SEP_bp; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DSZ DR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_bfa : apart b 8192 (sb + c * 4294967296 + 3758096384 + 4 * nf) (4 * Z.shiftr maxc 1)).
    { unfold apart. try (generalize alloc_ceiling_val); clear - BFORM KBR CR NF0 NFH HH8; try pose proof alloc_ceiling_val. lia. }
    pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp); (p, p + 8); (mh, mh + 4); (2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880, 2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880 + rq);
               (thr + 2840, thr + 2856); (C + 80 * c, C + 80 * c + 4); (ri + 128 * c, ri + 128 * c + 8)] m) as MU.
    unfold free_array_of in K.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    unfold dorec_callblk.
    eapply (dorec_call_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m b i pw); [> try (fside CV) .. | idtac].
    rewrite <- (Z_to_bv_bv_unsigned pw), PW. unfold cbrec_entry.
    (* [comment removed for export] *)
    eapply (CBPRIM _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m
              (bv_unsigned sp + 8) mh sb ri c idx d mu n b1 lo old); rewrite <- ?HSZ, <- ?HP, <- ?HR8; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?HSZ, <- ?HP, <- ?HR8, ?SHE, ?RQ; first [kcell | fside CV | exact MAG]).
    intros ra1 t0b t1b t2b a0b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b m1 CF1 MAG1 HDR1 SHP1 MU1 WM1 MI1 ST1.
    unfold cbrec_frame in CF1. rewrite ?unsigned_lit in CF1, MU1, ST1 by lia. rewrite ?SHE, ?RQ in SHP1, MU1.
    kp MAG1. kp SHP1. clear MAG HDR SHC. kpost MU1 WM1.
    pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp); (thr + 2840, thr + 2856); (C + 80 * c, C + 80 * c + 4); (ri + 128 * c, ri + 128 * c + 8)] m1) as MUB.
    pose proof (wmono_refl rsegs m1) as WMB.
    unfold cbrec_tail.
    (* [comment removed for export] *)
    assert (TC1 : thread_cells m1 tp tsd ctx thr) by tcells TPL.
    eapply (cbrec_tailp_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1
              (bv_unsigned sp) lo (bv_unsigned sp + 8) C mh p sb c (idx * size) n CHUNK_INVALID b1 tsd ctx thr rf rfd);
      [> try (fside CV) .. | idtac].
    all: try (first [fside CV | right; lia | unfold CHUNK_INVALID; lia | zmod | exact (proj1 HDR1) | unfold apart in SEP_tm; lia]).
    intros t0c t1c t2c a4c a5c a6c a7c t3c t4c t5c t6c m2 TRF2 MU2 WM2 MI2 ST2.
    rewrite ?unsigned_lit in MU2, ST2 by lia.
    clear TRF CF1 TC1. kpost MU2 WM2.
    unfold lcdealloc_entry. rewrite (Z_to_bv_bv_unsigned sp).
    replace p with (sb + c * 4294967296 + 16 * k) at 1 by lia.
    (* [comment removed for export] *)
    assert (SEP_Cs : apart C 3888 sb (2^37)) by (revert SEP_ts; unfold apart; clear; intros; lia).
    assert (SEP_Cr : apart C 3888 ri 4096) by (revert SEP_tr; unfold apart; clear; intros; lia).
    eapply (cpush_drain_map_pre2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m2
              lo C c sb ri k maxc nf mfa ks statv nfs v88); rewrite <- ?HSZ; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?HSZ; unfold free_array_of, CF; first [kcell | fside CV | zmod | assumption]).
    intros t0e t1e t2e a6e t3e t4e t5e t6e lscr scr2 scr3 scr4 m3 LF DRF RTF EFF MFF LINE3 STA3 MX3 NFC3 MFA3 NFS3 MUc WMc MI3 ST3.
    unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret in LF, DRF, RTF, EFF, MFF.
    rewrite ?unsigned_lit in LF, DRF, RTF, EFF, MFF, MUc, ST3 by lia. rewrite <- ?HSZ in LINE3.
    clear LINE STA MX NFC MFA NFS. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Cthr2); kpost MUc WMc.
    (* [comment removed for export] *)
    unfold keep in MAG1, SHP1.
    eapply bytes_at_transport in SHP1; [| exact MUB | rewrite repeat_length; cbn [disjoint_from]; lia].
    assert (MAG3 : d = 0 \/ rw_cells rsegs m3 p [C8 (wz 0)]).
    { destruct MAG1 as [EE|CC]; [left; exact EE| right]. xfer CC MUB WMB. exact CC. }
    clear MAG1 MUB WMB.
    unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret, kFaMap, kFreeArrayOffset, mmap_ecall_pc, mapfixed_resume,
           dorec_retpc, lcdealloc_after, lcdrain_ret, rta_efasret, efas_mapret in *.
    replace (sb + c * 4294967296 + 16 * k) with p in RTF by lia.
    rewrite ?unsigned_lit by lia.
    eapply K.
    all: first [kcell | exact MAG3 | rewrite ?SHE, ?RQ; first [kcell | exact MU | eassumption] | rewrite ?HSZ; kcell | eassumption].
  Qed.

  (* [comment removed for export] *)
  #[using="BFORM TU TR DF CRI CSB SEP_tr SEP_ts SEP_sr RIAL RIHI RILO SBAL SBHI SBLO BLO THRA PCo TSDL TC SPA SPH CEIL ST MI ctx tsd Clg"] Lemma batch_free_drainmap_pre2 : forall (Q : machine_state -> Prop)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' statv : word)
      (nfs v88 : word) (tn tf tl ts maxc nf mfa : Z) (ks : list word),
    let E := C + 80 * 24 in let R := ri + 128 * 24 in let fa := free_array_of sb 24 in let h := Z.shiftr maxc 1 in
    let nm := round_up (4 * (nf + h)) kFaMap in let fe := sb + 24 * 4294967296 + kFreeArrayOffset + mfa in
    let D := E + 16 + 4 * (maxc - h) in
    lo <= bv_unsigned sp - 688 -> 0 <= tn < 2^64 -> T + 32 <= 2^47 -> T mod 8 = 0 -> 0 <= kb < 2^28 ->
    2 <= maxc <= 16 -> maxc mod 2 = 0 -> length ks = 16%nat -> 0 <= nf -> nf + h < 2^27 ->
    mfa < 4 * (nf + h) -> 0 <= mfa -> mfa mod kFaMap = 0 -> bv_unsigned ra0 mod 2 = 0 ->
    ro_cells rsegs m 0xb1d80 [C4 (wz 4294967295)] ->
    ro_cells rsegs m 0xb1d90 [C1 (Z_to_bv 8 0)] -> ro_cells rsegs m 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m (CF + 260) [C1 (Z_to_bv 8 0)] ->
    rw_cells rsegs m T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
    rw_cells rsegs m E [C4 (wz maxc); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m (R + 80) [C8 nfs; C8 v88] ->
    (forall (t0'' t1'' t2'' a6'' t3'' t4'' t5'' t6'' : word) (lscr scr2 scr3 scr4 : list byte) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        rw_cells rsegs m' (bv_unsigned sp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1d58) (wz T) (wz dorec_nextpc)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64 + -128)
                 (rta_frame scr2 (R + 8) s11 s10 s9' s8' s7' s6' (wz (2^37)) (wz b) (wz 24) (wz 0xb1d58) (wz C) (wz E) (wz lcdrain_ret)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (bv_unsigned sp + -48 + -56)) (wz 24) (wz nf) (wz R) (wz rta_efasret)) ->
        rw_cells rsegs m' (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)
                 (mapcb_frame scr4 (wz 0xb1d58) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) ->
        rw_cells rsegs m' E [C4 (wz (maxc - h)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
        rw_cells rsegs m' (C + 2576) [C8 statv] ->
        rw_cells rsegs m' R [C8 (wz kMutexWriter)] -> rw_cells rsegs m' (R + 16) [C8 (wz nf)] -> rw_cells rsegs m' (R + 24) [C8 (wz mfa)] ->
        rw_cells rsegs m' (R + 80) [C8 nfs; C8 v88] ->
        munch [(bv_unsigned sp - 688, bv_unsigned sp); (E, E + 4); (R, R + 8)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + -48 + -64 + -128 + -48 + -128) ->
        Q (MSsvc (mkR (wz mapfixed_resume) (wz (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)) gp tp t0'' t1'' t2'' (wz (nm - mfa)) (wz 1)
                      (wz fe) (wz (nm - mfa)) (wz 3) (wz 50) (wz (-1)) (wz 0) a6'' (wz 222)
                      (wz fe) (wz efas_name) (wz PSC) (wz h) (wz D) (wz (nf + h)) (wz 2305843009213693952)
                      (wz fa) (wz 1152921504607895551) (wz kMutexWriter) t3'' t4'' t5'' t6'')
                 F (wz mmap_ecall_pc) (wz 222) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' (wz T) (wz 0xb1d58) a0' a1' a2' a3' a4' a5' a6' a7'
                        (wz LMA_L) (wz LMA_STAT) (wz b) (wz (2^37)) s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                    F (wz dorec_batchblk) fc None m (seg_rom rsegs)).
  Proof. try clear CBPRIM. try clear TPE. try clear BHI. try clear BAL. try clear CNTB. try clear SEP_rs. try clear SEP_tc. try clear SEP_cs. try clear SEP_bt. try clear SEP_bc. try clear SEP_br. try clear KBR.   (* [comment removed for export] *)
    intros until ks. cbv zeta. intros LOLE TNR THI TAL KB MXR MXE LKS NF0 NFH NOFIT MFA0 MFAM RA0 CITV CPMH CGCF CDMP TCL LINE STA MX NFC MFA NFS K.
    pose proof (maxc_half maxc MXR MXE) as [MH HH8].
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold head_regs, kHighMemBeg, LMA_L, LMA_STAT, CF in *.
    pose proof (cbc_rw m DF) as CBC.
    pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp); (C + 80 * 24, C + 80 * 24 + 4); (ri + 128 * 24, ri + 128 * 24 + 8)] m) as MU.
    unfold free_array_of in K.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 b) with (Z_to_bv 64 (sb + 24 * 2^32 + 16 * kb)) by (rewrite BFORM; reflexivity).
    eapply (dorec_batch_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m sb kb (wz C));
      [> try (fside CV) .. | idtac].
    all: try (first [kcell | zmod | unfold apart in SEP_ts; lia]).
    unfold lcdealloc_entry.
    assert (SEP_Cs : apart C 3888 sb (2^37)) by (revert SEP_ts; unfold apart; clear; intros; lia).
    assert (SEP_Cr : apart C 3888 ri 4096) by (revert SEP_tr; unfold apart; clear; intros; lia).
    (* [comment removed for export] *)
    eapply (cpush_drain_map_pre2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
              lo C 24 sb ri kb maxc nf mfa ks statv nfs v88); rewrite <- ?BFORM; change (class_size 24) with 8192; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?BFORM; change (class_size 24) with 8192; unfold free_array_of, CF;
              first [kcell | fside CV | zmod | rewrite BFORM; f_equal; lia | assumption]).
    intros t0e t1e t2e a6e t3e t4e t5e t6e lscr scr2 scr3 scr4 m3 LF DRF RTF EFF MFF LINE3 STA3 MX3 NFC3 MFA3 NFS3 MUc WMc MI3 ST3.
    unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret in LF, DRF, RTF, EFF, MFF.
    rewrite ?unsigned_lit in LF, DRF, RTF, EFF, MFF, MUc, ST3 by lia. change (class_size 24) with 8192 in LINE3.
    clear LINE STA MX NFC MFA NFS. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CRI); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Cthr2); try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_Ctsd); kpost MUc WMc.
    unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret, kFaMap, kFreeArrayOffset, mmap_ecall_pc, mapfixed_resume,
           dorec_nextpc, lcdealloc_after, lcdrain_ret, rta_efasret, efas_mapret in *.
    replace (sb + 24 * 4294967296 + 16 * kb) with b in RTF by lia.
    rewrite ?unsigned_lit by lia.
    eapply K.
    all: first [kcell | exact MU | eassumption].
  Qed.
End DoRec3.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
