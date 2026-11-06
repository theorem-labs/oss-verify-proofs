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
Ltac hot_lia_cut := ltac2:(Ltac2.Control.enter (fun () => hot_lia_keep_existing [@LOLE; @CEIL; @RIHI; @CR; @CSR; @LKS; @LJ; @HH8; @SBLO; @SPR; @RILO; @MXR; @LBthr; @MFA0; @DR; @PIN; @Bthr'; @SEP_sr; @TR; @HP; @NM3; @CV; @SPH; @IR; @NM1; @HNB; @CNTB; @X; @FIT; @MUR; @NF0; @SB16; @TU; @BFORM; @LO0; @ISZ; @MHD; @SEP_Cr; @SZ16; @NR; @R81; @DSZ; @KBR; @SBHI; @SEP_ts; @NFH; @NOFIT; @HMA; @R8E; @RQ; @SEP_rm; @K1; @KLE; @SEP_tr; @Btp; @USZ; @MH; @K16; @SEP_tm; @SHV; @SZ8; @SEP_bt; @SEP_tp; @IDX0; @SEP_cs; @SEP_rs; @D16; @BHI; @BLO; @HyS; @Q1; @SEP_bp; @SEP_Cs; @Q0; @GQH; @CHK; @B2])).
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
Local Ltac tf_threshold ::= constr:(4%nat).   (* [comment removed for export] *)
Local Ltac transport_after_call segs m m' MU WM ::= tf_transport segs m m' MU WM.
(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require KDrop.
Ltac hot_kdrop := ltac2:(Ltac2.Control.enter (fun () => OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_ids [@Cthr2; @Ctsd]; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.kdrop_marked ())).
Local Ltac transport_after_call segs m m' MU WM ::= hot_kdrop; tf_transport segs m m' MU WM.
(* [comment removed for export] *)

(* [comment removed for export] *)
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaTwx2.
Ltac2 hot_tf_keep_existing names :=
  let hs := Ltac2.List.map (fun h => let (id, _, _) := h in id) (Ltac2.Control.hyps ()) in
  Ltac2.Std.keep (Ltac2.List.filter (fun n => Ltac2.List.exist (fun h => Ltac2.Ident.equal h n) hs) names).
Ltac hot_tf_cut := ltac2:(Ltac2.Control.enter (fun () => hot_tf_keep_existing [@RILO; @CR; @SBLO; @CEIL; @LOLE; @LBthr; @SBHI; @NF0; @MFA0; @SB16; @HMA; @Bctx'; @NFH; @SPH; @LBctx2; @NM1; @HNB; @BLO; @BHI])).
Ltac hot_tf_lia0 :=
  first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tran6di.tf_lia ::= hot_tf_cut; hot_tf_lia0.
(* [comment removed for export] *)
Section DoRec2.
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
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="BFORM TU TR DF CRI CSB SEP_tr SEP_ts SEP_rs SEP_sr RIAL RIHI RILO SBAL SBHI SBLO BLO THRA PCo TSDL TC SPA SPH CEIL ST MI ctx tsd Clg"] Lemma batch_free_drainfast : forall (Q : machine_state -> Prop)
      (ra' a0' a1' a2' a3' a4' a5' a6' a7' t0' t1' t2' t3' t4' t5' t6' s6' s7' s8' s9' statv : word)
      (nfs v88 : word) (tn tf tl ts maxc nf mfa : Z) (ks junk : list word),
    let E := C + 80 * 24 in let R := ri + 128 * 24 in let fa := free_array_of sb 24 in let h := Z.shiftr maxc 1 in
    lo <= bv_unsigned sp - 320 -> 0 <= tn < 2^64 -> T + 32 <= 2^47 -> T mod 8 = 0 -> 0 <= kb < 2^28 ->
    2 <= maxc <= 16 -> maxc mod 2 = 0 -> length ks = 16%nat -> length junk = Z.to_nat h -> 0 <= nf -> nf + h < 2^27 ->
    4 * (nf + h) <= mfa -> mfa < 2^64 -> bv_unsigned ra0 mod 2 = 0 ->
    ro_cells rsegs m 0xb1d80 [C4 (wz 4294967295)] ->
    rw_cells rsegs m T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
    rw_cells rsegs m E [C4 (wz maxc); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m (C + 2576) [C8 statv] ->
    rw_cells rsegs m R [C8 (wz 0)] -> rw_cells rsegs m (R + 16) [C8 (wz nf)] -> rw_cells rsegs m (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m (R + 80) [C8 nfs; C8 v88] -> u32arr rsegs m (fa + 4 * nf) junk ->
    (tn <> 0 -> forall (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz kb)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz mfa)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        munch [(bv_unsigned sp - 320, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (head_regs sp gp tp T s10 s11 (wz dorec_nextpc) tn a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (wz b) s6' s7' s8' s9')
                        F (wz dorec_head) fc None m' (seg_rom rsegs))) ->
    (tn = 0 -> forall (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz kb)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz mfa)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        munch [(bv_unsigned sp - 320, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h)] m m' ->
        wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + 112) ->
        evt rsegs Q (MS (mkR ra0 (wz (bv_unsigned sp + 112)) gp tp t0'' t1'' t2'' s0v s1v (wz 0) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR ra' sp gp tp t0' t1' t2' (wz T) (wz 0xb1d58) a0' a1' a2' a3' a4' a5' a6' a7'
                        (wz LMA_L) (wz LMA_STAT) (wz b) (wz (2^37)) s6' s7' s8' s9' s10 s11 t3' t4' t5' t6')
                    F (wz dorec_batchblk) fc None m (seg_rom rsegs)).
  Proof. try clear CBPRIM. try clear TPE. try clear BHI. try clear BAL. try clear CNTB. try clear SEP_tc. try clear SEP_cs. try clear SEP_bt. try clear SEP_bc. try clear SEP_br. try clear KBR.   (* [comment removed for export] *)
    intros until junk. cbv zeta. intros LOLE TNR THI TAL KB MXR MXE LKS LJ NF0 NFH FITF MFH RA0 CITV TCL LINE STA MX NFC MFA NFS DST KM K0.
    pose proof (maxc_half maxc MXR MXE) as [MH HH8].
    pose proof PCo as PC'. (first [ dand13 PC' as Ccan Cgotcf Cthr Cgotsh Cshoff Cgotmid Cgotmide Cgothi Chivars Cgotms Creal Cgotps Cps | destruct PC' as (Ccan & Cgotcf & Cthr & Cgotsh & Cshoff & Cgotmid & Cgotmide & Cgothi & Chivars & Cgotms & Creal & Cgotps & Cps) ]).
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof TC as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    unfold head_regs, kHighMemBeg, LMA_L, LMA_STAT in *.
    pose proof (cbc_rw m DF) as CBC.
    pose proof (munch_refl [(bv_unsigned sp - 320, bv_unsigned sp); (C + 80 * 24, C + 80 * 24 + 80); (C + 2576, C + 2584); (ri + 128 * 24, ri + 128 * 24 + 8);
               (ri + 128 * 24 + 16, ri + 128 * 24 + 24); (ri + 128 * 24 + 80, ri + 128 * 24 + 88);
               (sb + 24 * 4294967296 + 3758096384 + 4 * nf, sb + 24 * 4294967296 + 3758096384 + 4 * nf + 4 * Z.shiftr maxc 1)] m) as MU.
    unfold free_array_of in DST, KM, K0.
    pose proof (wmono_refl rsegs m) as WM.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 b) with (Z_to_bv 64 (sb + 24 * 2^32 + 16 * kb)) by (rewrite BFORM; reflexivity).
    eapply (dorec_batch_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m sb kb (wz C));
      [> try (fside CV) .. | idtac].
    all: try (first [kcell | zmod | unfold apart in SEP_ts; lia]).
    unfold lcdealloc_entry.
    assert (SEP_Cs : apart C 3888 sb (2^37)) by (revert SEP_ts; unfold apart; clear; intros; lia).
    assert (SEP_Cr : apart C 3888 ri 4096) by (revert SEP_tr; unfold apart; clear; intros; lia).
    eapply evt_cut; [eapply (cpush_drain_fast _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m
                               lo C 24 sb ri kb maxc nf mfa ks junk statv nfs v88)|]; rewrite <- ?BFORM; change (class_size 24) with 8192; [> try (fside CV) .. | idtac].
    all: try (unfold free_array_of; first [kcell | fside CV | zmod | rewrite BFORM; f_equal; lia | assumption]).
    intros ms' PO. unfold cpush_drain_fast_post, cpush_drain_W, free_array_of in PO. cbv zeta in PO. destruct_exs PO.
    (first [ dand12 PO as E3 MUc WMc MI3 ST3 LINE3 STA3 MX3 NFC3 MFA3 NFS3 DST3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & LINE3 & STA3 & MX3 & NFC3 & MFA3 & NFS3 & DST3) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST3 by lia. change (class_size 24) with 8192 in LINE3.
    clear LINE STA MX NFC MFA NFS DST. try (pose proof OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.KDrop.KdMark as kdm_CRI); kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 dorec_nextpc)) with (Z_to_bv 64 dorec_nextpc) by (symmetry; apply ret_pc_even; [unfold dorec_nextpc; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    assert (SPE : wz (bv_unsigned sp + 112 + -112) = sp) by (replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia; apply Z_to_bv_bv_unsigned).
    rewrite <- SPE at 1.
    eapply (dorec_next_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 (bv_unsigned sp + 112) lo T tn tf tl ts scr
              (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0); [> try (fside CV) .. | idtac].
    all: try (first [replace (bv_unsigned sp + 112 - 112) with (bv_unsigned sp) by lia; first [kcell | eassumption]
                    | replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia; first [kcell | eassumption] | right; lia | zmod]).
    - intros TNZ. replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      eapply (KM TNZ); first [kcell | exact MU | eassumption].
    - intros TZ ST4. eapply (K0 TZ); first [kcell | exact MU | eassumption].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="KBR BFORM kb SEP_bt SEP_cs SEP_tr SEP_ts SEP_rs SEP_sr RIAL RIHI RILO SBAL SBHI SBLO CNTB BHI BLO THRA TSDL SPA SPH CEIL ST m"] Lemma iter_prim_drainmap_post : forall (Q : machine_state -> Prop) (m7 : word -> option byte)
      (t0' t1' t2' a0r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' pw statv nfs v88 mm72 mm80 : word)
      (lscr scr2 scr3 scr4 old : list byte)
      (mh c idx d mu n b1 rf rfd maxc k nf mfa : Z) (ks junk : list word),
    let size := class_size c in let p := sb + c * 2^32 + idx * size in let r8 := round_up n 8 in let E := C + 80 * c in
    let R := ri + 128 * c in let fa := free_array_of sb c in let h := Z.shiftr maxc 1 in
    let nm := round_up (4 * (nf + h)) kFaMap in let fe := sb + c * 4294967296 + kFreeArrayOffset + mfa in
    let D := E + 16 + 4 * (maxc - h) in
    lo <= bv_unsigned sp - 688 -> 0 <= i < cnt -> mh = p + d -> 0 <= d < size -> d mod 16 = 0 -> 1 <= c <= 30 -> 0 <= idx -> (idx + 1) * size <= mu -> 0 <= mu <= 3758096384 ->
    16 * k = idx * size -> 1 <= n < 2^32 -> mh + 16 + r8 <= 2^47 -> d + 16 + r8 <= size ->
    2 <= maxc <= 16 -> maxc mod 2 = 0 -> length ks = 16%nat -> length junk = Z.to_nat h -> 0 <= nf -> nf + h < 2^27 ->
    mfa < 4 * (nf + h) -> 0 <= mfa -> mfa mod kFaMap = 0 -> apart b 8192 p size -> bv_unsigned a0r = fe ->
    bv_unsigned tp <= kShadowOffset -> tsd + 8 <= kShadowOffset ->
    mem_inv rsegs m7 -> stk rsegs m7 lo (bv_unsigned sp + -48 + -64 + -128 + -48 + -128) ->
    thread_cells m7 tp tsd ctx thr -> poison_consts m7 ->
    ro_cells rsegs m7 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m7 0xb1d88 [C8 (wz ri)] -> ro_cells rsegs m7 0xb1d80 [C4 (wz 4294967295)] ->
    ro_cells rsegs m7 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m7 (CF + 144) [C8 (wz 0)] ->
    rw_cells rsegs m7 (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m7 (b + 24 + 8 * i) [C8 pw] ->
    ro_cells rsegs m7 (ri + 128 * c + 48) [C8 (wz mu)] ->
    (d = 0 \/ rw_cells rsegs m7 p [C8 (wz 0)]) ->
    rw_cells rsegs m7 mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
    bytes_at rsegs m7 (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
    rw_cells rsegs m7 (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
    rw_cells rsegs m7 (bv_unsigned sp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1d58) (wz T) (wz dorec_retpc)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64 + -128)
             (rta_frame scr2 (R + 8) s11 s10 (wz (16 + i)) (wz (cnt + 16)) (wz (b + 152 + 8 * i)) (wz cnt) (wz (2^37)) (wz p) (wz c) (wz 0xb1d58) (wz C) (wz E) (wz lcdrain_ret)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (bv_unsigned sp + -48 + -56)) (wz c) (wz nf) (wz R) (wz rta_efasret)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)
             (mapcb_frame scr4 (wz 0xb1d58) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) ->
    rw_cells rsegs m7 E [C4 (wz (maxc - h)); C4 (wz maxc); C8 (wz size); CB 64 (u32s ks)] ->
    rw_cells rsegs m7 (C + 2576) [C8 statv] ->
    rw_cells rsegs m7 R [C8 (wz kMutexWriter)] -> rw_cells rsegs m7 (R + 16) [C8 (wz nf)] -> rw_cells rsegs m7 (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m7 (R + 80) [C8 nfs; C8 v88] -> u32arr rsegs m7 (fa + 4 * nf) junk ->
    rw_cells rsegs m7 (sh fe) [CB (Z.to_nat ((nm - mfa) / 8)) old] ->
    rw_cells rsegs m7 (thr + 2872) [C8 mm72; C8 mm80] ->
    (i + 1 < cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        ro_cells rsegs m' (ri + 128 * c + 48) [C8 (wz mu)] ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz size); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz k)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz nm)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        bytes_at rsegs m' (sh fe) (repeat (Z_to_bv 8 250) (Z.to_nat ((nm - mfa) / 8))) ->
        rw_cells rsegs m' (thr + 2872) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + (nm - mfa)))] ->
        munch [(bv_unsigned sp - 688, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 24, R + 32); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h); (sh fe, sh fe + (nm - mfa) / 8); (thr + 2872, thr + 2888)] m7 m' ->
        wmono rsegs m7 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_callblk) fc None m' (seg_rom rsegs))) ->
    (i + 1 = cnt -> forall (a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' (b + 24 + 8 * i) [C8 pw] ->
        ro_cells rsegs m' (ri + 128 * c + 48) [C8 (wz mu)] ->
        (d = 0 \/ rw_cells rsegs m' p [C8 (wz 0)]) ->
        rw_cells rsegs m' mh [C1 (Z_to_bv 8 CHUNK_INVALID); C1 (Z_to_bv 8 b1); C2 (wz (size_hi n)); C4 (wz n)] ->
        bytes_at rsegs m' (sh (mh + 16)) (repeat (Z_to_bv 8 kAsanHeapLeftRedzoneMagic) (Z.to_nat (r8 / 8))) ->
        rw_cells rsegs m' (thr + 2840) [C8 (wz (rf + 1)); C8 (wz (rfd + n))] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz size); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz k)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz nm)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        bytes_at rsegs m' (sh fe) (repeat (Z_to_bv 8 250) (Z.to_nat ((nm - mfa) / 8))) ->
        rw_cells rsegs m' (thr + 2872) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + (nm - mfa)))] ->
        munch [(bv_unsigned sp - 688, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 24, R + 32); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h); (sh fe, sh fe + (nm - mfa) / 8); (thr + 2872, thr + 2888)] m7 m' ->
        wmono rsegs m7 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (it_regs sp gp tp T b cnt s10 s11 (wz dorec_retpc) a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (i + 1))
                        F (wz dorec_batchblk) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz mapfixed_resume) (wz (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)) gp tp t0' t1' t2' (wz (nm - mfa)) (wz 1)
                        a0r a1' a2' a3' a4' a5' a6' a7'
                        (wz fe) (wz efas_name) (wz PSC) (wz h) (wz D) (wz (nf + h)) (wz 2305843009213693952)
                        (wz fa) (wz 1152921504607895551) (wz kMutexWriter) t3' t4' t5' t6')
                    F (wz mmap_after_pc) fc None m7 (seg_rom rsegs)).
  Proof. try clear CBPRIM. try clear TPE. try clear BAL. try clear SEP_tc. try clear SEP_bc. try clear SEP_br. try clear TR. try clear TU.   (* [comment removed for export] *)
    intros until junk. cbv zeta. intros LOLE IR MHD DR DAL CR IDX0 FIT MUR K16 NR MHR USZ MXR MXE LKS LJ NF0 NFH NOFIT MFA0 MFAM SEP_bp A0R TPLO TSDLO
           MI7 ST7 TC7 PC7 CSB7 CRI7 CITV7 CGCF7 CMLM7 DF7 ENT7 CMU7 MAG7 HDR7 SHP7 TRF7 LF DRF RTF EFF MFF LINE7 STA7 MX7 NFC7 MFC7 NFS7 DST7 SHC7 THS7 KM KD.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (maxc_half maxc MXR MXE) as [MH HH8].
    pose proof (class_size_range c CR) as CSR. unfold kMaxSize in CSR. pose proof (class_size_mod32 c CR) as CSM.
    pose proof (round_up_ge n 8 ltac:(lia)) as R81. pose proof (round_up_lt n 8 ltac:(lia)) as R82. pose proof (round_up_mod n 8 ltac:(lia)) as R83.
    pose proof TC7 as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    clear MI ST TC PCo CSB CRI DF.
    unfold it_regs, kHighMemBeg, RI_PTR, LMA_L, LMA_STAT, CF, kFaMap, kFreeArrayOffset, free_array_of in *.
    remember (round_up n 8) as r8 eqn:HR8. remember (class_size c) as size eqn:HSZ.
    remember (sb + c * 2^32 + idx * size) as p eqn:HP.
    assert (SZ16 : size = 16 * (size / 16)).
    { pose proof (Z_div_mod_eq_full size 16) as X. rewrite (mod0_down size 32 16 ltac:(exists 2; reflexivity) CSM) in X. lia. }
    assert (SB16 : sb = 16 * (sb / 16)).
    { pose proof (Z_div_mod_eq_full sb 16) as X. rewrite (mod0_down sb 4096 16 ltac:(exists 256; reflexivity) SBAL) in X. lia. }
    assert (R8E : r8 = 8 * (r8 / 8)) by (pose proof (Z_div_mod_eq_full r8 8) as X; rewrite R83 in X; lia).
    assert (D16 : d = 16 * (d / 16)) by (pose proof (Z_div_mod_eq_full d 16) as X; rewrite DAL in X; lia).
    set (sq := size / 16) in *. set (bq := sb / 16) in *. set (rq := r8 / 8) in *. set (dq := d / 16) in *.
    assert (RQ : r8 / 8 = rq) by reflexivity. clearbody sq bq rq dq.
    assert (ISZ : 0 <= idx * size) by (apply Z.mul_nonneg_nonneg; lia).
    assert (PIN : sb <= p /\ p + size <= sb + 2^37) by (rewrite HP; lia).
    assert (DSZ : d + 16 <= size) by lia.
    assert (SEP_tp : apart thr 4096 p size) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_tm : apart thr 4096 mh 16) by (revert SEP_ts; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DR DSZ; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cp : apart ctx 65536 p size) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_cm : apart ctx 65536 mh 16) by (revert SEP_cs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DR DSZ; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_bm : apart b 8192 mh 16) by (revert SEP_bp; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DR DSZ; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_rp : apart ri 4096 p size) by (revert SEP_rs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR; try pose proof alloc_ceiling_val; intros; lia).
    assert (SEP_rm : apart ri 4096 mh 16) by (revert SEP_rs; unfold apart; try (generalize alloc_ceiling_val); clear - PIN CR MHD DR DSZ; try pose proof alloc_ceiling_val; intros; lia).
    (* [comment removed for export] *)
    assert (SHU : sh (mh + 16) = 2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2 + 2147450880).
    { unfold sh, kShadowOffset. rewrite MHD, HP, SB16, SZ16, D16.
      replace (16 * bq + c * 2 ^ 32 + idx * (16 * sq) + 16 * dq + 16) with ((2 * bq + c * 536870912 + 2 * idx * sq + 2 * dq + 2) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    assert (HMA : mfa = 8 * (mfa / 8)).
    { pose proof (Z_div_mod_eq_full mfa 8) as X. rewrite (mod0_down mfa 262144 8 ltac:(exists 32768; reflexivity) MFAM) in X. lia. }
    pose proof (roundup_famap_range (4 * (nf + Z.shiftr maxc 1)) ltac:(lia)) as [NM1 NM2]. pose proof (roundup_famap_cap (4 * (nf + Z.shiftr maxc 1)) ltac:(lia)) as NM3.
    remember (round_up (4 * (nf + Z.shiftr maxc 1)) 262144) as nmv eqn:HNM.
    assert (HNB : nmv = 8 * (nmv / 8)).
    { pose proof (Z_div_mod_eq_full nmv 8) as X. rewrite (mod0_down nmv 262144 8 ltac:(exists 32768; reflexivity) NM2) in X. lia. }
    set (ma := mfa / 8) in *. set (nb8 := nmv / 8) in *. clearbody ma nb8.
    assert (SHV : sh (sb + c * 4294967296 + 3758096384 + mfa) = 2 * bq + c * 536870912 + 469762048 + ma + 2147450880).
    { unfold sh, kShadowOffset. rewrite SB16, HMA. replace (16 * bq + c * 4294967296 + 3758096384 + 8 * ma) with ((2 * bq + c * 536870912 + 469762048 + ma) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    assert (SZ8 : (nmv - mfa) / 8 = nb8 - ma) by (rewrite HMA, HNB; replace (8 * nb8 - 8 * ma) with ((nb8 - ma) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    rewrite ?SHU in *. rewrite ?SHV in *. rewrite ?SZ8 in *.
    (* [comment removed for export] *)
    kp MAG7. kp SHP7. kp HDR7. kp TRF7. kp ENT7. kp CMU7.
    pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp); (C + 80 * c, C + 80 * c + 80); (C + 2576, C + 2584); (ri + 128 * c, ri + 128 * c + 8);
                            (ri + 128 * c + 16, ri + 128 * c + 24); (ri + 128 * c + 24, ri + 128 * c + 32); (ri + 128 * c + 80, ri + 128 * c + 88);
                            (sb + c * 4294967296 + 3758096384 + 4 * nf, sb + c * 4294967296 + 3758096384 + 4 * nf + 4 * Z.shiftr maxc 1);
                            (2 * bq + c * 536870912 + 469762048 + ma + 2147450880, 2 * bq + c * 536870912 + 469762048 + ma + 2147450880 + (nb8 - ma));
                            (thr + 2872, thr + 2888)] m7) as MU.
    pose proof (wmono_refl rsegs m7) as WM.
    assert (SEP_Cs : apart C 3888 sb (2^37)) by (revert SEP_ts; unfold apart; clear; intros; lia).
    assert (SEP_Cr : apart C 3888 ri 4096) by (revert SEP_tr; unfold apart; clear; intros; lia).
    unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret, kFaMap, kFreeArrayOffset, free_array_of in *.
    (* [comment removed for export] *)
    rewrite HNM.
    eapply evt_cut; [eapply (cpush_drain_map_post_ok _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo C c sb ri k maxc nf mfa ks junk statv nfs v88)|];
      rewrite <- ?HSZ, <- ?HNM, ?SHV, ?SZ8; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?HSZ, <- ?HNM, ?SHV, ?SZ8; unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret, kFaMap, kFreeArrayOffset, free_array_of, CF;
              rewrite <- ?HNM, ?SHV, ?SZ8;
              first [kcell | fside CV | zmod | assumption | replace (sb + c * 4294967296 + 16 * k) with p by lia; kcell]).
    intros ms' PO. unfold cpush_drain_map_post, cpush_drain_map_W, free_array_of, kFreeArrayOffset, kFaMap in PO. cbv zeta in PO.
    rewrite <- ?HNM, ?SHV, ?SZ8 in PO. destruct_exs PO.
    (first [ dand14 PO as E3 MUc WMc MI3 ST3 LINE3 STA3 MX3 NFC3 MFA3 NFS3 DST3 SHF3 THS3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & LINE3 & STA3 & MX3 & NFC3 & MFA3 & NFS3 & DST3 & SHF3 & THS3) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST3 by lia. rewrite <- ?HSZ in LINE3.
    kp SHF3. clear LF DRF RTF EFF MFF LINE7 STA7 MX7 NFC7 MFC7 NFS7 DST7 SHC7 THS7. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 dorec_retpc)) with (Z_to_bv 64 dorec_retpc) by (symmetry; apply ret_pc_even; [unfold dorec_retpc; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    unfold keep in MAG7, SHP7, HDR7, TRF7, ENT7, CMU7, SHF3.
    xfer HDR7 MU WM. xfer TRF7 MU WM. xfer ENT7 MU WM. xfer CMU7 MU WM.
    assert (ISQ : idx * size = 16 * (idx * sq)) by (rewrite SZ16; lia).
    eapply bytes_at_transport in SHP7; [| exact MU | rewrite repeat_length; cbn [disjoint_from]; lia].
    assert (MAG3 : d = 0 \/ rw_cells rsegs m3 p [C8 (wz 0)]).
    { destruct MAG7 as [EE|CC]; [left; exact EE| right]. xfer CC MU WM. exact CC. }
    clear MAG7.
    (* [comment removed for export] *)
    unfold dorec_retpc.
    eapply (dorec_ret_ok _ sp gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 b i cnt); [kung; lia | kung; lia | kung; lia | kung; lia | |].
    - intros LT. eapply (KM LT); first [kcell | exact MAG3 | exact MU | rewrite ?HSZ; kcell | eassumption].
    - intros EQ. eapply (KD EQ); first [kcell | exact MAG3 | exact MU | rewrite ?HSZ; kcell | eassumption].
  Qed.
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="BFORM TU TR SEP_tr SEP_ts SEP_rs SEP_sr RIAL RIHI RILO SBAL SBHI SBLO BLO THRA TSDL SPA SPH CEIL ST m"] Lemma batch_free_drainmap_post : forall (Q : machine_state -> Prop) (m7 : word -> option byte)
      (t0' t1' t2' a0r a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' s6' s7' s8' s9' statv nfs v88 mm72 mm80 : word)
      (lscr scr2 scr3 scr4 old : list byte)
      (tn tf tl ts maxc nf mfa : Z) (ks junk : list word),
    let E := C + 80 * 24 in let R := ri + 128 * 24 in let fa := free_array_of sb 24 in let h := Z.shiftr maxc 1 in
    let nm := round_up (4 * (nf + h)) kFaMap in let fe := sb + 24 * 4294967296 + kFreeArrayOffset + mfa in
    let D := E + 16 + 4 * (maxc - h) in
    lo <= bv_unsigned sp - 688 -> 0 <= tn < 2^64 -> T + 32 <= 2^47 -> T mod 8 = 0 -> 0 <= kb < 2^28 ->
    2 <= maxc <= 16 -> maxc mod 2 = 0 -> length ks = 16%nat -> length junk = Z.to_nat h -> 0 <= nf -> nf + h < 2^27 ->
    mfa < 4 * (nf + h) -> 0 <= mfa -> mfa mod kFaMap = 0 -> bv_unsigned ra0 mod 2 = 0 -> bv_unsigned a0r = fe ->
    bv_unsigned tp <= kShadowOffset -> tsd + 8 <= kShadowOffset ->
    mem_inv rsegs m7 -> stk rsegs m7 lo (bv_unsigned sp + -48 + -64 + -128 + -48 + -128) ->
    thread_cells m7 tp tsd ctx thr -> poison_consts m7 ->
    ro_cells rsegs m7 0xb1d78 [C8 (wz sb)] -> ro_cells rsegs m7 0xb1d88 [C8 (wz ri)] -> ro_cells rsegs m7 0xb1d80 [C4 (wz 4294967295)] ->
    ro_cells rsegs m7 0xa9180 [C8 (wz CF)] -> ro_cells rsegs m7 (CF + 144) [C8 (wz 0)] ->
    rw_cells rsegs m7 (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
    rw_cells rsegs m7 T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
    rw_cells rsegs m7 (bv_unsigned sp + -48) (lcd_frame (wz b) (wz LMA_STAT) (wz LMA_L) (wz 0xb1d58) (wz T) (wz dorec_nextpc)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64) (lcdrain_frame lscr (wz lcdealloc_after)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64 + -128)
             (rta_frame scr2 (R + 8) s11 s10 s9' s8' s7' s6' (wz (2^37)) (wz b) (wz 24) (wz 0xb1d58) (wz C) (wz E) (wz lcdrain_ret)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64 + -128 + -48) (efas_frame scr3 (wz (bv_unsigned sp + -48 + -56)) (wz 24) (wz nf) (wz R) (wz rta_efasret)) ->
    rw_cells rsegs m7 (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)
             (mapcb_frame scr4 (wz 0xb1d58) (wz R) (wz (nm - mfa)) fe (nm - mfa) (wz fe) (wz nm) (wz efas_mapret)) ->
    rw_cells rsegs m7 E [C4 (wz (maxc - h)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s ks)] ->
    rw_cells rsegs m7 (C + 2576) [C8 statv] ->
    rw_cells rsegs m7 R [C8 (wz kMutexWriter)] -> rw_cells rsegs m7 (R + 16) [C8 (wz nf)] -> rw_cells rsegs m7 (R + 24) [C8 (wz mfa)] ->
    rw_cells rsegs m7 (R + 80) [C8 nfs; C8 v88] -> u32arr rsegs m7 (fa + 4 * nf) junk ->
    rw_cells rsegs m7 (sh fe) [CB (Z.to_nat ((nm - mfa) / 8)) old] ->
    rw_cells rsegs m7 (thr + 2872) [C8 mm72; C8 mm80] ->
    (tn <> 0 -> forall (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz kb)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz nm)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        bytes_at rsegs m' (sh fe) (repeat (Z_to_bv 8 250) (Z.to_nat ((nm - mfa) / 8))) ->
        rw_cells rsegs m' (thr + 2872) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + (nm - mfa)))] ->
        munch [(bv_unsigned sp - 688, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 24, R + 32); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h); (sh fe, sh fe + (nm - mfa) / 8); (thr + 2872, thr + 2888)] m7 m' ->
        wmono rsegs m7 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp) ->
        evt rsegs Q (MS (head_regs sp gp tp T s10 s11 (wz dorec_nextpc) tn a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' (wz b) s6' s7' s8' s9')
                        F (wz dorec_head) fc None m' (seg_rom rsegs))) ->
    (tn = 0 -> forall (a1'' a2'' a3'' a4'' a5'' a6'' a7'' t0'' t1'' t2'' t3'' t4'' t5'' t6'' statv' : word) (m' : word -> option byte),
        rw_cells rsegs m' (bv_unsigned sp) (dorec_frame scr (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0) ->
        rw_cells rsegs m' T [C8 (wz tn); C8 (wz tf); C8 (wz tl); C8 (wz ts)] ->
        rw_cells rsegs m' E [C4 (wz (maxc - h + 1)); C4 (wz maxc); C8 (wz 8192); CB 64 (u32s (upd ks (Z.to_nat (maxc - h)) (wz kb)))] ->
        rw_cells rsegs m' (C + 2576) [C8 statv'] ->
        rw_cells rsegs m' R [C8 (wz 0)] -> rw_cells rsegs m' (R + 16) [C8 (wz (nf + h))] -> rw_cells rsegs m' (R + 24) [C8 (wz nm)] ->
        rw_cells rsegs m' (R + 80) [C8 (wz (bv_unsigned nfs + h)); C8 v88] ->
        u32arr rsegs m' (fa + 4 * nf) (firstn (Z.to_nat h) (skipn (Z.to_nat (maxc - h)) ks)) ->
        bytes_at rsegs m' (sh fe) (repeat (Z_to_bv 8 250) (Z.to_nat ((nm - mfa) / 8))) ->
        rw_cells rsegs m' (thr + 2872) [C8 (wz (bv_unsigned mm72 + 1)); C8 (wz (bv_unsigned mm80 + (nm - mfa)))] ->
        munch [(bv_unsigned sp - 688, bv_unsigned sp); (E, E + 80); (C + 2576, C + 2584); (R, R + 8); (R + 16, R + 24); (R + 24, R + 32); (R + 80, R + 88);
               (fa + 4 * nf, fa + 4 * nf + 4 * h); (sh fe, sh fe + (nm - mfa) / 8); (thr + 2872, thr + 2888)] m7 m' ->
        wmono rsegs m7 m' -> mem_inv rsegs m' -> stk rsegs m' lo (bv_unsigned sp + 112) ->
        evt rsegs Q (MS (mkR ra0 (wz (bv_unsigned sp + 112)) gp tp t0'' t1'' t2'' s0v s1v (wz 0) a1'' a2'' a3'' a4'' a5'' a6'' a7''
                            s2v s3v s4v s5v s6v s7v s8v s9v s10 s11 t3'' t4'' t5'' t6'')
                        F (ret_pc ra0) fc None m' (seg_rom rsegs))) ->
    evt rsegs Q (MS (mkR (wz mapfixed_resume) (wz (bv_unsigned sp + -48 + -64 + -128 + -48 + -128)) gp tp t0' t1' t2' (wz (nm - mfa)) (wz 1)
                        a0r a1' a2' a3' a4' a5' a6' a7'
                        (wz fe) (wz efas_name) (wz PSC) (wz h) (wz D) (wz (nf + h)) (wz 2305843009213693952)
                        (wz fa) (wz 1152921504607895551) (wz kMutexWriter) t3' t4' t5' t6')
                    F (wz mmap_after_pc) fc None m7 (seg_rom rsegs)).
  Proof. try clear CBPRIM. try clear TPE. try clear BHI. try clear BAL. try clear CNTB. try clear SEP_tc. try clear SEP_cs. try clear SEP_bt. try clear SEP_bc. try clear SEP_br. try clear KBR.   (* [comment removed for export] *)
    intros until junk. cbv zeta. intros LOLE TNR THI TAL KB MXR MXE LKS LJ NF0 NFH NOFIT MFA0 MFAM RA0 A0R TPLO TSDLO
           MI7 ST7 TC7 PC7 CSB7 CRI7 CITV7 CGCF7 CMLM7 DF7 TCL7 LF DRF RTF EFF MFF LINE7 STA7 MX7 NFC7 MFC7 NFS7 DST7 SHC7 THS7 KM K0.
    pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
    assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
    pose proof (maxc_half maxc MXR MXE) as [MH HH8].
    pose proof TC7 as TC'. (first [ dand6 TC' as Cini Ckey Ctsd Cctx Cthr2 Bnds | destruct TC' as (Cini & Ckey & Ctsd & Cctx & Cthr2 & Bnds) ]).
    (first [ dand8 Bnds as Btsd Btsd' Bctx Bctx' Bthr Bthr' Btp Bctx2 | destruct Bnds as (Btsd & Btsd' & Bctx & Bctx' & Bthr & Bthr' & Btp & Bctx2) ]). free_lin.
    clear MI ST TC PCo CSB CRI DF.
    unfold head_regs, kHighMemBeg, RI_PTR, LMA_L, LMA_STAT, CF, kFaMap, kFreeArrayOffset, free_array_of in *.
    assert (SB16 : sb = 16 * (sb / 16)).
    { pose proof (Z_div_mod_eq_full sb 16) as X. rewrite (mod0_down sb 4096 16 ltac:(exists 256; reflexivity) SBAL) in X. lia. }
    set (bq := sb / 16) in *. clearbody bq.
    assert (HMA : mfa = 8 * (mfa / 8)).
    { pose proof (Z_div_mod_eq_full mfa 8) as X. rewrite (mod0_down mfa 262144 8 ltac:(exists 32768; reflexivity) MFAM) in X. lia. }
    pose proof (roundup_famap_range (4 * (nf + Z.shiftr maxc 1)) ltac:(lia)) as [NM1 NM2]. pose proof (roundup_famap_cap (4 * (nf + Z.shiftr maxc 1)) ltac:(lia)) as NM3.
    remember (round_up (4 * (nf + Z.shiftr maxc 1)) 262144) as nmv eqn:HNM.
    assert (HNB : nmv = 8 * (nmv / 8)).
    { pose proof (Z_div_mod_eq_full nmv 8) as X. rewrite (mod0_down nmv 262144 8 ltac:(exists 32768; reflexivity) NM2) in X. lia. }
    set (ma := mfa / 8) in *. set (nb8 := nmv / 8) in *. clearbody ma nb8.
    assert (SHV : sh (sb + 24 * 4294967296 + 3758096384 + mfa) = 2 * bq + 24 * 536870912 + 469762048 + ma + 2147450880).
    { unfold sh, kShadowOffset. rewrite SB16, HMA. replace (16 * bq + 24 * 4294967296 + 3758096384 + 8 * ma) with ((2 * bq + 24 * 536870912 + 469762048 + ma) * 8) by lia.
      rewrite Z.div_mul by lia. reflexivity. }
    assert (SZ8 : (nmv - mfa) / 8 = nb8 - ma) by (rewrite HMA, HNB; replace (8 * nb8 - 8 * ma) with ((nb8 - ma) * 8) by lia; rewrite Z.div_mul by lia; reflexivity).
    rewrite ?SHV in *. rewrite ?SZ8 in *.
    pose proof (munch_refl [(bv_unsigned sp - 688, bv_unsigned sp); (C + 80 * 24, C + 80 * 24 + 80); (C + 2576, C + 2584); (ri + 128 * 24, ri + 128 * 24 + 8);
                            (ri + 128 * 24 + 16, ri + 128 * 24 + 24); (ri + 128 * 24 + 24, ri + 128 * 24 + 32); (ri + 128 * 24 + 80, ri + 128 * 24 + 88);
                            (sb + 24 * 4294967296 + 3758096384 + 4 * nf, sb + 24 * 4294967296 + 3758096384 + 4 * nf + 4 * Z.shiftr maxc 1);
                            (2 * bq + 24 * 536870912 + 469762048 + ma + 2147450880, 2 * bq + 24 * 536870912 + 469762048 + ma + 2147450880 + (nb8 - ma));
                            (thr + 2872, thr + 2888)] m7) as MU.
    pose proof (wmono_refl rsegs m7) as WM.
    assert (SEP_Cs : apart C 3888 sb (2^37)) by (revert SEP_ts; unfold apart; clear; intros; lia).
    assert (SEP_Cr : apart C 3888 ri 4096) by (revert SEP_tr; unfold apart; clear; intros; lia).
    unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret, kFaMap, kFreeArrayOffset, free_array_of in *.
    (* [comment removed for export] *)
    rewrite HNM.
    eapply evt_cut; [eapply (cpush_drain_map_post_ok (wz dorec_nextpc) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo C 24 sb ri kb maxc nf mfa ks junk statv nfs v88)|];
      rewrite <- ?BFORM, <- ?HNM, ?SHV, ?SZ8; change (class_size 24) with 8192; [> try (fside CV) .. | idtac].
    all: try (rewrite <- ?BFORM, <- ?HNM, ?SHV, ?SZ8; change (class_size 24) with 8192;
              unfold lcd_frame, lcdrain_frame, rta_frame, efas_frame, mapcb_frame, map_ret, kFaMap, kFreeArrayOffset, free_array_of, CF;
              rewrite <- ?HNM, ?SHV, ?SZ8;
              first [kcell | fside CV | zmod | assumption | rewrite BFORM; f_equal; lia
                    | replace (sb + 24 * 4294967296 + 16 * kb) with b by lia; kcell]).
    intros ms' PO. unfold cpush_drain_map_post, cpush_drain_map_W, free_array_of, kFreeArrayOffset, kFaMap in PO. cbv zeta in PO.
    rewrite <- ?HNM, ?SHV, ?SZ8 in PO. destruct_exs PO.
    (first [ dand14 PO as E3 MUc WMc MI3 ST3 LINE3 STA3 MX3 NFC3 MFA3 NFS3 DST3 SHF3 THS3 | destruct PO as (E3 & MUc & WMc & MI3 & ST3 & LINE3 & STA3 & MX3 & NFC3 & MFA3 & NFS3 & DST3 & SHF3 & THS3) ]). subst ms'.
    rewrite ?unsigned_lit in MUc, ST3 by lia. change (class_size 24) with 8192 in LINE3.
    clear LF DRF RTF EFF MFF LINE7 STA7 MX7 NFC7 MFC7 NFS7 DST7 SHC7 THS7. kpost MUc WMc.
    replace (ret_pc (Z_to_bv 64 dorec_nextpc)) with (Z_to_bv 64 dorec_nextpc) by (symmetry; apply ret_pc_even; [unfold dorec_nextpc; lia|reflexivity]).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
    (* [comment removed for export] *)
    assert (SPE : wz (bv_unsigned sp + 112 + -112) = sp) by (replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia; apply Z_to_bv_bv_unsigned).
    rewrite <- SPE at 1.
    eapply (dorec_next_ok _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m3 (bv_unsigned sp + 112) lo T tn tf tl ts scr
              (wz C) cbs s9v s8v s7v s6v s5v s4v s3v s2v s1v s0v ra0); [> try (fside CV) .. | idtac].
    all: try (first [replace (bv_unsigned sp + 112 - 112) with (bv_unsigned sp) by lia; first [kcell | eassumption]
                    | replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia; first [kcell | eassumption] | right; lia | zmod]).
    - intros TNZ. replace (bv_unsigned sp + 112 + -112) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      eapply (KM TNZ); first [kcell | exact MU | eassumption].
    - intros TZ ST4. eapply (K0 TZ); first [kcell | exact MU | eassumption].
  Qed.
End DoRec2.

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma recycle_enter : forall (ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
    (q qmin hi gl gqb lo : Z) (bs : list (Z * Z)) (Q : machine_state -> Prop),
  let gn := Z.of_nat (length bs) in let k := npop qmin gqb bs in let kz := Z.of_nat k in let psum := lsum (firstn k bs) in
  let T := bv_unsigned sp - 80 in
  mem_inv rsegs m -> stk rsegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - 192 -> alloc_ceiling <= lo -> bv_unsigned sp <= 2^47 ->
  0x10000 <= q -> q + 192 <= 0x60a000 -> q mod 8 = 0 ->     (* [comment removed for export] *)
  0 <= hi < 2^15 -> 0 <= qmin < 2^64 -> 0 <= gqb -> gqb * 100 < 2^64 -> gn < 2^24 -> 0 <= gl < 2^64 ->
  gn * 8192 <= gqb -> (gn * 16384 <= gqb \/ gqb <= gn * 8192) -> lsum bs <= gqb -> gqb - lsum bs <= qmin ->
  bwf bs -> bchain m bs -> (1 <= k)%nat -> bv_unsigned sp mod 8 = 0 ->
  rw_cells rsegs m (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 1); C2 (wz hi)] ->
  rw_cells rsegs m (q + 160) [C8 (wz gn); C8 (wz (baddr bs 0)); C8 (wz gl); C8 (wz gqb)] ->
  (forall (t0' t1' t2' a4' a5' a6' a7' : word) (scr : list byte) (m' : word -> option byte),
      rw_cells rsegs m' T [C8 (wz kz); C8 (wz (baddr bs 0)); C8 (wz (baddr bs (k - 1))); C8 (wz psum)] ->
      rw_cells rsegs m' (T + 32) [C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
      rw_cells rsegs m' (T - 112) (dorec_frame scr a2 a3 s9 s8 s7 s6 s5 s4 s3 s2 s1 s0 (wz recycle_ret)) ->
      rw_cells rsegs m' (q + 152) [C1 (Z_to_bv 8 0); C1 (Z_to_bv 8 0); C2 (wz hi)] ->
      rw_cells rsegs m' (q + 160) [C8 (wz (gn - kz)); C8 (wz (baddr bs k));
                                   C8 (wz (if ((k =? length bs)%nat && (0 <? k)%nat)%bool then 0 else gl)); C8 (wz (gqb - psum))] ->
      bchain_cut m' bs k ->
      munch ((bv_unsigned sp - 192, bv_unsigned sp) :: (q + 152, q + 156) :: (q + 160, q + 192) :: bivls (firstn k bs)) m m' ->
      wmono rsegs m m' -> mem_inv rsegs m' -> stk rsegs m' lo (T - 112) ->
      evt rsegs Q (MS (head_regs (wz (T - 112)) gp tp T s10 s11 (wz recycle_ret) kz (wz 0xb23e0) a2 a3 a4' a5' a6' a7' t0' t1' t2' t3 t4 t5 t6
                              s4 s6 s7 s8 s9)
                      F (wz dorec_head) fc None m' (seg_rom rsegs))) ->
  evt rsegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz q) (wz qmin) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (wz recycle_entry) fc None m (seg_rom rsegs)).
Proof.
  intros until Q. cbv zeta.
  intros MI ST LOLE CEIL SPH Q0 Q1 QAL HIR QMN GQ0 GQH GNH GLR CHK NOMERGE SUMLE SUMSTOP WF BC K1 SPA LCK GL K.
  pose proof alloc_ceiling_val as CV. free_lin. pose proof (zr_word sp) as SPR; unfold inr64 in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (npop_le_length qmin bs gqb) as KLE.
  unfold head_regs, kHighMemBeg in *.
  eapply (recycle_pre_ok _ _ gp tp t0 t1 t2 s0 s1 _ _ a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m q qmin hi gl gqb lo bs);
    cbv zeta; [> try (fside CV) .. | idtac].
  all: try assumption.
  intros t0' t1' t2' a4' a5' a6' a7' m1 RF LCK1 GL1 BCC MU1 WM1 MI1 ST1.
  rewrite ?unsigned_lit in RF, MU1, ST1 by lia. unfold recycle_frame in RF.
  replace (if (npop qmin gqb bs =? 0)%nat then 0 else baddr bs 0) with (baddr bs 0) in RF by (destruct (npop qmin gqb bs); [lia| reflexivity]).
  replace (if (npop qmin gqb bs =? 0)%nat then 0 else baddr bs (npop qmin gqb bs - 1)) with (baddr bs (npop qmin gqb bs - 1)) in RF
    by (destruct (npop qmin gqb bs); [lia| reflexivity]).
  apply (rw_cells_app_split m1 _ [C8 (wz (Z.of_nat (npop qmin gqb bs))); C8 (wz (baddr bs 0)); C8 (wz (baddr bs (npop qmin gqb bs - 1))); C8 (wz (lsum (firstn (npop qmin gqb bs) bs)))] _) in RF as [TC RREST].
  cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in RREST.
  clear LCK GL MI ST.
  unfold recycle_ret, dorec_entry.
  (* [comment removed for export] *)
  eapply (dorec_entryS_ok _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s10 s11 _ _ _ _ F fc m1
            (bv_unsigned sp - 80) lo (Z.of_nat (npop qmin gqb bs)) (baddr bs 0) (baddr bs (npop qmin gqb bs - 1)) (lsum (firstn (npop qmin gqb bs) bs)));
    [> try (fside CV) .. | idtac].
  all: try (first [kcell | rewrite ?unsigned_lit by lia; first [kcell | lia | right; lia | zmod]]).
  intros scr m2 DF TC2 MU2 WM2 MI2 ST2. rewrite ?unsigned_lit in DF, MU2, ST2 by lia.
  (* [comment removed for export] *)
  assert (MUF : munch ((bv_unsigned sp - 192, bv_unsigned sp) :: (q + 152, q + 156) :: (q + 160, q + 192) :: bivls (firstn (npop qmin gqb bs) bs)) m m2).
  { intros y Hy. cbn [outside] in Hy. destruct Hy as [HyS HyR].
    rewrite (MU2 y); [apply MU1; cbn [outside]; split; [try (generalize alloc_ceiling_val); clear -HyS; try pose proof alloc_ceiling_val; lia| exact HyR] |]. cbn [outside]. split; [try (generalize alloc_ceiling_val); clear -HyS; try pose proof alloc_ceiling_val; lia| exact I]. }
  assert (WMF : wmono rsegs m m2) by (eapply wmono_trans; [exact WM1| exact WM2]).
  xfer RREST MU2 WM2. xfer LCK1 MU2 WM2. xfer GL1 MU2 WM2.
  assert (BCC2 : bchain_cut m2 bs (npop qmin gqb bs)).
  { intros j Hj. pose proof (BCC j Hj) as X. destruct WF as [WF1 _]. (first [ pose proof ((WF1 j Hj)) as dR_17; dand3 dR_17 as B1 B2 _ | pose proof (WF1 j Hj) as (B1 & B2 & _) ]).
    xfer X MU2 WM2. exact X. }
  rewrite ?unsigned_lit by lia. unfold dorec_head.
  replace (bv_unsigned sp - 80 + -112) with (bv_unsigned sp - 80 - 112) by lia.
  eapply K.
  all: first [kcell | exact BCC2 | exact MUF | exact WMF | eassumption
             | replace (bv_unsigned sp - 80 - 112) with (bv_unsigned sp - 80 + -112) by lia; first [kcell | eassumption]
             | replace (bv_unsigned sp - 80 + 32) with (bv_unsigned sp + -80 + 32) by lia; first [kcell | eassumption] ].
Qed.

End CEIL.
Ltac slia ::= first [ exact I | lia | split; [lia|exact I] ].
