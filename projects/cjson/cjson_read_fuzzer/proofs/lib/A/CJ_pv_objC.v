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
From Stdlib Require Permutation.
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
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_common.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_cases.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_calls.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_lits.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_numK.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require NElim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Module CJ_pv_objA.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_lits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numK OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr.CJ_pv_arrA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr.CJ_pv_arrB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

Section OBJA.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis STRLEN : strlen_icpt_spec.
  Hypothesis REC : forall d, (d < n)%nat -> print_value_at AI TI d.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.


  Ltac steq := unfold CASE_ST, mkR, SHR, ASHBASE; repeat (lazymatch goal with |- @eq Z _ _ => lia | |- _ => first [reflexivity | progress f_equal] end).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition OBJ_LOC (loc : list word) : Prop :=
    nth_error loc 1 = Some (Z_to_bv 64 ASHBASE) /\ nth_error loc 2 = Some (SHR (PB + 16)) /\ nth_error loc 3 = Some (SHR PB)
    /\ nth_error loc 4 = Some (Z_to_bv 64 Fr) /\ nth_error loc 5 = Some (Z_to_bv 64 (PB + 16))
    /\ nth_error loc 6 = Some (Z_to_bv 64 (PB + 36)) /\ nth_error loc 7 = Some (SHR (PB + 36)).
  Definition OBJ_LOCC (loc : list word) : Prop :=
    nth_error loc 6 = Some (Z_to_bv 64 (PB + 36)) /\ nth_error loc 7 = Some (SHR (PB + 36)).
  Lemma obj_locc_of : forall loc, OBJ_LOC loc -> OBJ_LOCC loc.
  Proof. intros loc nelH_; (nelim nelH_ 7%nat; intros _ _ _ _ _ A6 A7). split; assumption. Qed.
  Lemma obj_loc9 : forall loc, length loc = 9%nat -> OBJ_LOC loc ->
    exists w0 w8, loc = [w0; Z_to_bv 64 ASHBASE; SHR (PB + 16); SHR PB; Z_to_bv 64 Fr; Z_to_bv 64 (PB + 16); Z_to_bv 64 (PB + 36); SHR (PB + 36); w8].
  Proof.
    intros loc LL nelH_; (nelim nelH_ 7%nat; intros A1 A2 A3 A4 A5 A6 A7). (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 ->).
    cbn in A1, A2, A3, A4, A5, A6, A7. injection A1 as ->. injection A2 as ->. injection A3 as ->. injection A4 as ->. injection A5 as ->. injection A6 as ->. injection A7 as ->.
    exists w0, w8. reflexivity.
  Qed.
  Lemma obj_loc9c : forall loc, length loc = 9%nat -> OBJ_LOCC loc ->
    exists w0 w1 w2 w3 w4 w5 w8, loc = [w0; w1; w2; w3; w4; w5; Z_to_bv 64 (PB + 36); SHR (PB + 36); w8].
  Proof.
    intros loc LL (A6 & A7). (nelim (loc9 loc LL) 10%nat; intros w0 w1 w2 w3 w4 w5 w6 w7 w8 ->).
    cbn in A6, A7. injection A6 as ->. injection A7 as ->. exists w0, w1, w2, w3, w4, w5, w8. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma tab_loop1 : forall (k : nat) (i : Z) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx D
      (x1 x5 x6 x7 x11 x13 x14 x15 x16 x17 x18 x22 x24 x28 x29 x30 x31 : word),
    Z.of_nat k = D - i -> 0 <= i < D -> off + D + 1 <= len -> 0 <= D ->
    PVX Q D mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx ->
    evt asegs (fun ms' => exists mm' bs' (x13' x14' : word),
                 ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) (Z_to_bv 64 D) (Z_to_bv 64 D) x13' x14' x15 x16 x17
                              x18 (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (SHR (PB + 24)) x22 (Z_to_bv 64 9) x24 (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
                          Fx (Z_to_bv 64 0x8409c) fcx None mm' (seg_rom asegs)
                 /\ PVX Q D mm' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs' loc jb SHP_IDLE Fx fcx)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) x11 (Z_to_bv 64 i) x13 x14 x15 x16 x17
               x18 (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (SHR (PB + 24)) x22 (Z_to_bv 64 9) x24 (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x8405c) fcx None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until x31; intros Hk Hi ROOM D0 CTXX; [lia|]. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN _ MI _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as [_ SOB].
    pose proof (shadow_ok_shchk1 mm buf len (buf + off + i) SOB ltac:(lia)) as CK.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    unfold PBS, wz in PBS1.
    pose proof (munch_refl [(buf + off + i, buf + off + i + 1)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zstep. zstep. zstep. sepM. asan_chk CK.
    ustore_at buf off (buf + off + i) i (wb 9) ltac:(reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    assert (CTX2 : PVX Q D m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off (upd bs (Z.to_nat (off + i)) (wb 9)) loc jb SHP_IDLE Fx fcx).
    { eapply (pvx_out_store Q PVL) with (W := [(buf + off + i, buf + off + i + 1)]);
        [exact CTXX| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARR| rewrite upd_length; reflexivity]. }
    pose proof (stack_shb0 mm (PB + 24) SSZ ltac:(lia)) as Z24. asan_chk Z24.
    zstep. zstep. zstep. if_cases K; zify_cond K.
    - eapply (IH (i + 1)); [lia| lia| exact ROOM| exact D0| exact CTX2].
    - zstep. apply evt_done. replace (i + 1) with D by lia. nexists 4%nat. split; [reflexivity| exact CTX2].
  Qed.

  Lemma tab_loop2 : forall (k : nat) (i : Z) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx D
      (x1 x5 x6 x7 x11 x14 x15 x16 x17 x18 x22 x23 x24 x28 x29 x30 x31 : word),
    Z.of_nat k = D - 1 - i -> 0 <= i < D - 1 -> off + D + 1 <= len -> 0 <= D ->
    PVX Q D mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx ->
    evt asegs (fun ms' => exists mm' bs' (x14' x15' : word),
                 ms' = MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) (Z_to_bv 64 (D - 1)) (Z_to_bv 64 (D - 1)) (Z_to_bv 64 9) x14' x15' x16 x17
                              x18 (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (SHR (PB + 24)) x22 x23 x24 (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
                          Fx (Z_to_bv 64 0x84a28) fcx None mm' (seg_rom asegs)
                 /\ PVX Q D mm' mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs' loc jb SHP_IDLE Fx fcx)
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf + off)) x11 (Z_to_bv 64 i) (Z_to_bv 64 9) x14 x15 x16 x17
               x18 (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (SHR (PB + 24)) x22 x23 x24 (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x849c8) fcx None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros until x31; intros Hk Hi ROOM D0 CTXX; [lia|]. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 9%nat; intros HL HP PBS1 ARR LEN PN _ MI _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HL HP. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HL (perm_in_head _ _ _ HP)) as [_ SOB].
    pose proof (shadow_ok_shchk1 mm buf len (buf + off + i) SOB ltac:(lia)) as CK.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    unfold PBS, wz in PBS1.
    pose proof (munch_refl [(buf + off + i, buf + off + i + 1)] mm) as MU. pose proof (wmono_refl asegs mm) as WM.
    zstep. zstep. zstep. sepM. asan_chk CK.
    ustore_at buf off (buf + off + i) i (wb 9) ltac:(reflexivity).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m2 end.
    assert (CTX2 : PVX Q D m2 mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off (upd bs (Z.to_nat (off + i)) (wb 9)) loc jb SHP_IDLE Fx fcx).
    { eapply (pvx_out_store Q PVL) with (W := [(buf + off + i, buf + off + i + 1)]);
        [exact CTXX| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARR| rewrite upd_length; reflexivity]. }
    pose proof (stack_shb0 mm (PB + 24) SSZ ltac:(lia)) as Z24. asan_chk Z24.
    zstep. zstep. zstep. zstep. if_cases K; zify_cond K.
    - eapply (IH (i + 1)); [lia| lia| exact ROOM| exact D0| exact CTX2].
    - zstep. apply evt_done. replace (i + 1) with (D - 1) by lia. nexists 4%nat. split; [reflexivity| exact CTX2].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma obj_close2 : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx (needed : Z)
      (x1 x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 : word),
    PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> OBJ_LOCC loc ->
    needed = (if fz Q then 2 else dep + 2) ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 (Z_to_bv 64 needed) x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (SHR (PB + 24)) x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x84988) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX OLC ND. lits. bandM. sepM. unfold SHR, ASHBASE.
    assert (FZR : 0 <= Z.b2z (fz Q) <= 1) by (destruct (fz Q); cbn; lia).
    assert (NDR : 2 <= needed <= dep + 2) by (destruct (fz Q); lia).
    pose proof CTXX as [CTX FRX]. (nelimp CTX 7%nat; intros HL HP _ _ _ PN _). (nelimp PN 3%nat; intros PN1 PN2 PN3).
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS); [exact CTXX| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x84990)) with (Z_to_bv 64 0x84990) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [(-> & EX) | (buf' & len' & bs' & -> & NZ' & CTX2 & ROOM & L31)].
    { (* [comment removed for export] *)
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K; zify_cond K; [| exfalso; apply K; reflexivity]. clear K.
      apply evt_done. cbv beta. eapply (pv_epi' Q PVL FLAGLOW). exact EX. }
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 9%nat; intros HLb HPb PBSb ARRb LENb PNb _ MIb _). (nelimp FRXb 4%nat; intros _ LOC LL _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
    (nelim (obj_loc9c loc LL OLC) 8%nat; intros w0 w1 w2 w3 w4 w5 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HLb HPb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    unfold PBS, wz in PBSb.
    (* [comment removed for export] *)
    assert (JN : forall mq bsq (T : Z) (x11q x12q x13q x14q x15q : word),
      PVX Q (dep + 1) mq mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off bsq loc jb SHP_IDLE Fx fcx ->
      0 <= T -> off + T + 2 + 1 <= len' ->
      LSCPS asegs POST
        (MS (mkR (Z_to_bv 64 0x84990) (Z_to_bv 64 SA) gp tp t0' t1' t2' sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf' + off + T)) x11q x12q x13q x14q x15q a6' a7'
                x18 (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (Z_to_bv 64 (Z.shiftr (PB + 24) 3 + 2147450880)) x22 x23 (Z_to_bv 64 Fr) (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
            Fx (Z_to_bv 64 0x84a2c) fcx None mq (seg_rom asegs)) mo2 g2).
    { intros mq bsq T x11q x12q x13q x14q x15q CTXq T0 ROOMq. clear LOC PBSb ARRb.
      pose proof CTXq as [CTXc FRXc]. (nelimp CTXc 9%nat; intros HLc HPc PBSc ARRc LENc PNc _ MIc _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLc (perm_in_head _ _ _ HPc)) as [_ SOB].
      pose proof (shadow_ok_shchk1 mq buf' len' (buf' + off + T) SOB ltac:(lia)) as CK0.
      pose proof (shadow_ok_shchk1 mq buf' len' (buf' + off + T + 1) SOB ltac:(lia)) as CK1.
      pose proof (munch_refl [(buf' + off + T, buf' + off + T + 2)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. sepM. asan_chk CK0.
      zstep. zstep. ustore_at buf' off (buf' + off + T) T (wb 125) ltac:(reflexivity).
      zstep. zstep. sepM. asan_chk CK1.
      ustore_at buf' off (buf' + off + T + 1) (T + 1) (wb 0) ltac:(reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      assert (CTX3 : PVX Q (dep + 1) m3 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd (upd bsq (Z.to_nat (off + T)) (wb 125)) (Z.to_nat (off + (T + 1))) (wb 0)) loc jb SHP_IDLE Fx fcx).
      { eapply (pvx_out_store Q PVL) with (W := [(buf' + off + T, buf' + off + T + 2)]);
          [exact CTXq| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRc| rewrite !upd_length; reflexivity]. }
      clear MU WM CTXq CTXc FRXc HLc PBSc SSZc SOB.
      pose proof CTX3 as [CTXd FRXd]. (nelimp CTXd 4%nat; intros _ _ PBSd _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXd)))))))))))) as SSZd.
      unfold PBS, wz in PBSd.
      pose proof (munch_refl [(PB, PB + 32)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      pose proof (stack_shb0 m3 (PB + 24) SSZd ltac:(lia)) as Z24. asan_chk Z24.
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
      zstep. apply evt_done. cbv beta.
      assert (CTX4 : PVM Q dep m4 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd (upd bsq (Z.to_nat (off + T)) (wb 125)) (Z.to_nat (off + (T + 1))) (wb 0))).
      { eapply (pvm_dep_store Q PVL (dep + 1) dep); [exact CTXd| exact MU| exact WM| assumption| | lia].
        unfold PBS, wz. replace (dep + 1 - 1) with dep in * by lia. assumption. }
      eapply (pv_ret1 Q PVL FLAGLOW). eapply (pvx_exit1 Q PVL).
      + split; [exact CTX4|]. eapply (pvfr_wext Q PVL); [exact FRXd| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor].
      + exists (T + 1). split; [lia|]. split; [lia|]. rewrite nth_error_upd_same by (rewrite upd_length; pose proof (proj1 (proj2 (proj2 (proj2 (proj2 CTXd))))); lia). reflexivity. }
    (* [comment removed for export] *)
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases K; zify_cond K; [exfalso; lia|]. clear K.
    zstep. pose proof (stack_shb0 m2 (PB + 36) SSZb ltac:(lia)) as Z36. asan_chk Z36.
    zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
    - (* [comment removed for export] *)
      assert (Efz : fz Q = true) by (unfold fz; apply Z.ltb_lt; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia). rewrite Efz in ND.
      apply evt_done. cbv beta. replace (buf' + off) with (buf' + off + 0) by lia.
      eapply JN; [exact CTX2| lia| lia].
    - assert (Efz : fz Q = false) by (unfold fz; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia). rewrite Efz in ND.
      pose proof (stack_shb0 m2 (PB + 24) SSZb ltac:(lia)) as Z24. asan_chk Z24.
      zstep. zstep. zstep. if_cases K1; zify_cond K1.
      + (* [comment removed for export] *)
        apply evt_done. cbv beta. replace (buf' + off) with (buf' + off + 0) by lia.
        eapply JN; [exact CTX2| lia| lia].
      + zstep. zstep.
        eapply evt_cut.
        { eapply (tab_loop2 (Z.to_nat dep) 0) with (D := dep + 1); [lia| lia| | lia| exact CTX2]. lia. }
        cbv beta. intros ms' nelH_; (nelim nelH_ 6%nat; intros mm' bsq x14' x15' -> CTXq).
        zstep. apply evt_done. cbv beta.
        eapply JN; [exact CTXq| lia| lia].
  Qed.

  Lemma obj_close : forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x22 x23 x28 x29 x30 x31 : word),
    PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> OBJ_LOCC loc ->
    LSCPS asegs POST
      (MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
              x18 (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (SHR (PB + 24)) x22 x23 (Z_to_bv 64 Fr) (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
          Fx (Z_to_bv 64 0x847e4) fcx None mm (seg_rom asegs)) mo1 g1.
  Proof.
    intros until x31. intros CTXX OLC. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 7%nat; intros HL HP PBS1 _ _ PN _). (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    (nelim (obj_loc9c loc LL OLC) 8%nat; intros w0 w1 w2 w3 w4 w5 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC.
    unfold PBS, wz in PBS1.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. pose proof (stack_shb0 mm (PB + 36) SSZ ltac:(lia)) as Z36. asan_chk Z36.
    zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
    - assert (Efz : fz Q = true) by (unfold fz; apply Z.ltb_lt; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia).
      zstep. apply evt_done. cbv beta.
      eapply lscps_eq; [| eapply (obj_close2 mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx 2); [exact CTXX| exact OLC| rewrite Efz; reflexivity]]. steq.
    - assert (Efz : fz Q = false) by (unfold fz; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia).
      pose proof (stack_shb0 mm (PB + 24) SSZ ltac:(lia)) as Z24. asan_chk Z24.
      zstep. zstep. zstep. apply evt_done. cbv beta.
      eapply lscps_eq; [| eapply (obj_close2 mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx (dep + 2)); [exact CTXX| exact OLC| rewrite Efz; reflexivity]]. steq.
  Qed.
End OBJA.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
End CJ_pv_objA.

(* [comment removed for export] *)
Module CJ_pv_objB.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool Stdlib.Sorting.Permutation.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_bandM OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_tree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pvalue_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_common OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_cases OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_calls OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_lits OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_numK OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr.CJ_pv_arrA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr.CJ_pv_arrB OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr CJ_pv_objA OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

Section OBJB.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis STRLEN : strlen_icpt_spec.
  Hypothesis REC : forall d, (d < n)%nat -> print_value_at AI TI d.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.


  Hypothesis PSTR : pstr_stmt AI TI.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition OST (pc : Z) (c : Z) (mm : word -> option byte) (Fx : bvmap 5 word) (fcx : bv 32)
      (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 : word) : machine_state :=
    MS (mkR x1 (Z_to_bv 64 SA) gp tp x5 x6 x7 sp (Z_to_bv 64 SA) x10 x11 x12 x13 x14 x15 x16 x17
            (SHR (PB + 16)) (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (SHR (PB + 24)) (Z_to_bv 64 c) x23 x24 (SHR Fr) (Z_to_bv 64 Fr) (Z_to_bv 64 ASHBASE) x28 x29 x30 x31)
       Fx (Z_to_bv 64 pc) fcx None mm (seg_rom asegs).

  (* [comment removed for export] *)
  Definition OKAT (pc c : Z) : Prop :=
    forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word),
      PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> OBJ_LOC Q loc ->
      LSCPS asegs POST (OST pc c mm Fx fcx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 9) (Z_to_bv 64 Fr) x28 x29 x30 x31) mo1 g1.
  (* [comment removed for export] *)
  Definition OKATF (pc c : Z) : Prop :=
    forall mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb Fx fcx
           (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31 : word),
      PVX Q (dep + 1) mm mo1 g1 LB1 TRS1 B1 np1 errv1 buf len off bs loc jb SHP_IDLE Fx fcx -> OBJ_LOC Q loc ->
      LSCPS asegs POST (OST pc c mm Fx fcx x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x23 x24 x28 x29 x30 x31) mo1 g1.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma obj_ind : forall c, OKAT 0x840b8 c -> OKAT 0x84010 c.
  Proof.
    intros c K. unfold OKAT, OST. intros until x31. intros CTXX OL. lits. bandM. sepM. unfold SHR, ASHBASE.
    assert (FZR : 0 <= Z.b2z (fz Q) <= 1) by (destruct (fz Q); cbn; lia).
    pose proof CTXX as [CTX FRX]. (nelimp CTX 7%nat; intros HL HP PBS1 _ _ PN _). (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    (nelim (obj_loc9 Q loc LL OL) 3%nat; intros w0 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC.
    unfold PBS, wz in PBS1.
    unfold OKAT, OST in K. unfold SHR, ASHBASE in K.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. pose proof (stack_shb0 mm (PB + 36) SSZ ltac:(lia)) as Z36. asan_chk Z36.
    zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
    { (* [comment removed for export] *)
      apply evt_done. cbv beta. eapply K; [exact CTXX| exact OL]. }
    pose proof (stack_shb0 mm (PB + 24) SSZ ltac:(lia)) as Z24. asan_chk Z24.
    zstep. zstep. zstep. apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS); [exact CTXX| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x84040)) with (Z_to_bv 64 0x84040) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [(-> & EX) | (buf' & len' & bs' & -> & NZ' & CTX2 & ROOM & L31)].
    { eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta. eapply (pv_epi' Q PVL FLAGLOW). exact EX. }
    clear LOC PBS1 Z36 Z24 SSZ.
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 4%nat; intros HLb HPb PBSb _). (nelimp FRXb 3%nat; intros _ LOC _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HLb HPb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC. unfold PBS, wz in PBSb.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    pose proof (stack_shb0 m2 (PB + 24) SSZb ltac:(lia)) as Z24. asan_chk Z24.
    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|]. clear K1.
    zstep.
    eapply evt_cut.
    { eapply (tab_loop1 Q PVL (Z.to_nat (dep + 1)) 0) with (D := dep + 1); [lia| lia| | lia| exact CTX2]. lia. }
    cbv beta. intros ms' nelH_; (nelim nelH_ 6%nat; intros m3 bs3 x13' x14' -> CTX3). clear PBSb LOC Z24 SSZb. cbv beta delta [mkR].
    pose proof CTX3 as [CTXc FRXc]. (nelimp CTXc 9%nat; intros _ _ PBSc _ _ _ _ MIc _). (nelimp FRXc 3%nat; intros _ LOC _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
    rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC. unfold PBS, wz in PBSc.
    (* [comment removed for export] *)
    pose proof (stack_shb0 m3 (PB + 16) SSZc ltac:(lia)) as Z16. asan_chk Z16.
    pose proof (munch_refl [(PB, PB + 32)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    apply evt_done. cbv beta.
    assert (CTX4 : PVX Q (dep + 1) m4 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' (off + (dep + 1)) bs3 loc jb SHP_IDLE Fx fcx).
    { split.
      - eapply (pvm_off_store Q PVL); [exact CTXc| exact MU| exact WM| assumption| | lia].
        unfold PBS, wz. lazymatch goal with H : rw_cells asegs m4 PB _ |- _ => exact H end.
      - eapply (pvfr_wext Q PVL); [exact FRXc| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
    eapply K; [exact CTX4| exact OL].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma obj_key : forall c nx pv ch ty p1 vs vi p2 vd ky Bk,
    rw_cells asegs m c (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> In (c, 64) B -> cj_str m ky Bk -> (forall b, In b Bk -> In b B) ->
    OKAT 0x84160 c -> OKAT 0x840b8 c.
  Proof.
    intros c nx pv ch ty p1 vs vi p2 vd ky Bk ND CIN SK SUBK K. unfold OKAT, OST. intros until x31. intros CTXX OL. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp CTX 7%nat; intros HL HP _ _ _ PN _). (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    (nelim (obj_loc9 Q loc LL OL) 3%nat; intros w0 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC.
    destruct (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND CIN) as (NDm & _ & (C1 & C2 & _ & C4) & CIN1).
    unfold node_cells, wz in NDm. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
    pose proof (nd_shb0 AI _ _ _ _ _ _ _ _ _ c 56 HL CIN1 ltac:(lia) ltac:(lia) eq_refl) as SH56.
    unfold OKAT, OST in K. unfold SHR, ASHBASE in K.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep. asan_chk SH56.
    zstep. zstep. zstep. apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_pstr Q PVL PSTR); [exact CTXX| exact SK| exact SUBK| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO. clear LOC NDm SH56.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fx' fcx' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x840dc)) with (Z_to_bv 64 0x840dc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_step_evt. cbv beta delta [mkR].
    destruct OUT as [(-> & EX) | (-> & buf2 & len2 & off2 & bs2 & CTX2 & NUL2)].
    { zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta. eapply (pv_epi' Q PVL FLAGLOW). exact EX. }
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 4%nat; intros HLb HPb PBSb _). (nelimp FRXb 3%nat; intros _ LOC _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HLb HPb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC. unfold PBS, wz in PBSb.
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))) as PNb. (nelim PNb 3%nat; intros PNb1 PNb2 PNb3).
    (* [comment removed for export] *)
    zstep. pose proof (stack_shb0 m2 PB SSZb ltac:(lia)) as Z0. asan_chk Z0.
    zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
    pose proof (stack_shb0 m2 (PB + 16) SSZb ltac:(lia)) as Z16. asan_chk Z16.
    do 6 zstep. zstep. zstep. zstep. zstep.
    eapply evt_cut. { eapply (pvx_strlen_off Q PVL STRLEN); [exact CTX2| exact NUL2]. }
    cbv beta. intros ms' PO. clear Z0 Z16 PBSb LOC SSZb.
    (nelim PO 21%nat; intros k u0' u1' u2' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' m3 -> CTX3 K0 K1 KN).
    replace (ret_pc (Z_to_bv 64 0x8412c)) with (Z_to_bv 64 0x8412c) by (symmetry; apply ret_pc_even; [lia| reflexivity]). cbv beta delta [mkR].
    pose proof CTX3 as [CTXc FRXc]. (nelimp CTXc 9%nat; intros _ _ PBSc _ _ _ _ MIc _). (nelimp FRXc 3%nat; intros _ LOC _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
    rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC. unfold PBS, wz in PBSc.
    pose proof (stack_shb0 m3 (PB + 16) SSZc ltac:(lia)) as Z16. asan_chk Z16.
    pose proof (munch_refl [(PB, PB + 32)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    assert (CTX4 : PVX Q (dep + 1) m4 mo2 g2 LB2 TRS2 B2 np2 errv2 buf2 len2 (k + off2) bs2 loc jb SHP_IDLE Fx' fcx').
    { split.
      - eapply (pvm_off_store Q PVL); [exact CTXc| exact MU| exact WM| assumption| | lia].
        unfold PBS, wz. lazymatch goal with H : rw_cells asegs m4 PB _ |- _ => exact H end.
      - eapply (pvfr_wext Q PVL); [exact FRXc| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    apply evt_done. cbv beta. eapply K; [exact CTX4| exact OL].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma obj_colon : forall c, OKATF 0x841e8 c -> OKAT 0x84160 c.
  Proof.
    intros c K. unfold OKAT, OKATF, OST. intros until x31. intros CTXX OL. lits. bandM. sepM. unfold SHR, ASHBASE.
    assert (FZR : 0 <= Z.b2z (fz Q) <= 1) by (destruct (fz Q); cbn; lia).
    pose proof CTXX as [CTX FRX]. (nelimp CTX 7%nat; intros HL HP PBS1 _ _ PN _). (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    (nelim (obj_loc9 Q loc LL OL) 3%nat; intros w0 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC.
    unfold PBS, wz in PBS1.
    unfold OKATF, OST in K. unfold SHR, ASHBASE in K.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. pose proof (stack_shb0 mm (PB + 36) SSZ ltac:(lia)) as Z36. asan_chk Z36.
    zstep. zstep. zstep. zstep. zstep. zstep.
    (* [comment removed for export] *)
    match goal with |- context [Z_to_bv 64 (Z.b2z ?b + 1)] =>
      replace (Z.b2z b + 1) with (2 - Z.b2z (fz Q)) by (unfold fz; pose proof (bv_unsigned_in_range 64 (sx32 fw)); destruct (Z.ltb_spec (bv_unsigned (sx32 fw)) 1); destruct b eqn:Eb; cbn; first [lia | exfalso; revert Eb; rewrite ?Z.eqb_eq, ?Z.eqb_neq, ?negb_true_iff, ?negb_false_iff, ?Z.eqb_eq, ?Z.eqb_neq; lia])
    end.
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS); [exact CTXX| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO. clear LOC PBS1 Z36 SSZ.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x84184)) with (Z_to_bv 64 0x84184) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [(-> & EX) | (buf' & len' & bs' & -> & NZ' & CTX2 & ROOM & L31)].
    { eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta. eapply (pv_ret0_2c8 Q PVL FLAGLOW); [exact EX| rewrite EL; reflexivity]. }
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 9%nat; intros HLb HPb PBSb ARRb LENb PNb _ MIb _). (nelimp FRXb 3%nat; intros _ LOC _).
    (nelimp PNb 3%nat; intros PNb1 PNb2 PNb3).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HLb HPb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) as [_ SOB].
    pose proof (shadow_ok_shchk1 m2 buf' len' (buf' + off) SOB ltac:(lia)) as CK0.
    assert (CK1 : fz Q = false -> shchk m2 (buf' + off + 1) 1) by (intros E; eapply shadow_ok_shchk1; [exact SOB| rewrite E in ROOM; cbn in ROOM; lia]).
    rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC. unfold PBS, wz in PBSb.
    pose proof (munch_refl [(buf' + off, buf' + off + 2)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    zstep. zstep. sepM. asan_chk CK0.
    zstep. ustore_at buf' off (buf' + off) 0 (wb 58) ltac:(reflexivity).
    zstep. pose proof (stack_shb0 m2 (PB + 36) SSZb ltac:(lia)) as Z36. asan_chk Z36.
    zstep. zstep.
    (* [comment removed for export] *)
    assert (JN : forall mq (bsq : list byte) x10q x11q x12q,
      u8arr asegs mq buf' bsq -> length bsq = length bs' ->
      munch [(buf' + off, buf' + off + 2)] m2 mq -> wmono asegs m2 mq -> mem_inv asegs mq ->
      evt asegs (fun ms' => LSCPS asegs POST ms' mo2 g2)
        (MS (mkR (Z_to_bv 64 0x84184) (Z_to_bv 64 SA) gp tp t0' t1' t2' sp (Z_to_bv 64 SA) x10q x11q x12q a3' a4' a5' a6' a7'
                (Z_to_bv 64 (Z.shiftr (PB + 16) 3 + 2147450880)) (Z_to_bv 64 PB) (Z_to_bv 64 (PB + 24)) (Z_to_bv 64 (Z.shiftr (PB + 24) 3 + 2147450880)) (Z_to_bv 64 c) (Z_to_bv 64 9) (Z_to_bv 64 (2 - Z.b2z (fz Q)))
                (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
            Fx (Z_to_bv 64 0x841d0) fcx None mq (seg_rom asegs))).
    { intros mq bsq x10q x11q x12q ARRq LBS MUq WMq MIq. clear ARRb MU WM.
      assert (CTXq : PVX Q (dep + 1) mq mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off bsq loc jb SHP_IDLE Fx fcx).
      { eapply (pvx_out_store Q PVL) with (W := [(buf' + off, buf' + off + 2)]);
          [exact CTX2| exact MUq| exact WMq| exact MIq| constructor; [cbn [fst snd]; lia| constructor]| exact ARRq| exact LBS]. }
      clear MUq WMq ARRq.
      pose proof CTXq as [CTXc FRXc]. (nelimp CTXc 9%nat; intros _ _ PBSc _ _ _ _ MIc _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
      unfold PBS, wz in PBSc. cbv beta delta [mkR].
      pose proof (stack_shb0 mq (PB + 16) SSZc ltac:(lia)) as Z16. asan_chk Z16.
      pose proof (munch_refl [(PB, PB + 32)] mq) as MU2. pose proof (wmono_refl asegs mq) as WM2.
      zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      apply evt_done. cbv beta.
      assert (CTX3 : PVX Q (dep + 1) m3 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' (off + (2 - Z.b2z (fz Q))) bsq loc jb SHP_IDLE Fx fcx).
      { split.
        - eapply (pvm_off_store Q PVL); [exact CTXc| exact MU2| exact WM2| assumption| | lia].
          unfold PBS, wz. lazymatch goal with H : rw_cells asegs m3 PB _ |- _ => exact H end.
        - eapply (pvfr_wext Q PVL); [exact FRXc| exact MU2| exact WM2|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
      eapply K; [exact CTX3| exact OL]. }
    zstep. if_cases Kf; zify_cond Kf.
    - (* [comment removed for export] *)
      eapply JN; [exact ARRb| rewrite upd_length; reflexivity| exact MU| exact WM| assumption].
    - assert (Efz : fz Q = false) by (unfold fz; apply Z.ltb_ge; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia).
      specialize (CK1 Efz).
      zstep. zstep. zstep. sepM. asan_chk CK1.
      ustore_at buf' off (buf' + off + 1) 1 (wb 9) ltac:(reflexivity).
      eapply JN; [exact ARRb| rewrite !upd_length; reflexivity| exact MU| exact WM| assumption].
  Qed.
End OBJB.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
End CJ_pv_objB.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require LiaOn.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.LiaOn.SepM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_bandM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pwlopts_A.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pwlopts_A.CJ_band3.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs CJ_iface AShadow CJ_tree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_pbuf.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pvalue_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_ctx.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_ctx.CJ_fp_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.CJ_print_lemmas2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_ctx CJ_pv_common CJ_pv_cases CJ_pv_calls CJ_pv_lits CJ_pv_numK.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr.CJ_pv_arrA.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pv_arr.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pv_arr.CJ_pv_arrB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_pv_arr.
Import CJ_pv_objA.
Import CJ_pv_objB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_pstrA.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_pstrA.CJ_shfast.
Local Ltac sh_resolve_if ::= sh_resolve_if_fast.
Local Ltac sh_join v Cv rdk ::= sh_join_fast v Cv rdk.
(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require StoreCache.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.StoreCache.StoreFast.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import StoreCache.
Local Ltac mem_after_store ::= mem_after_store_cached.
Local Ltac addr_eq_tac ::= addr_eq_tac_cached.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_cached segs m m' MU WM.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.

Section OBJC.
  Variable Q : pvi.
  Local Notation AI := (q_ai Q).    Local Notation TI := (q_ti Q).
  Local Notation ra := (q_ra Q).    Local Notation sp := (q_sp Q).    Local Notation gp := (q_gp Q).    Local Notation tp := (q_tp Q).
  Local Notation s0 := (q_s0 Q).    Local Notation s1 := (q_s1 Q).    Local Notation s2 := (q_s2 Q).    Local Notation s3 := (q_s3 Q).
  Local Notation s4 := (q_s4 Q).    Local Notation s5 := (q_s5 Q).    Local Notation s6 := (q_s6 Q).    Local Notation s7 := (q_s7 Q).
  Local Notation s8 := (q_s8 Q).    Local Notation s9 := (q_s9 Q).    Local Notation s10 := (q_s10 Q).  Local Notation s11 := (q_s11 Q).
  Local Notation F := (q_F Q).      Local Notation m := (q_m Q).      Local Notation g := (q_g Q).
  Local Notation sp0 := (q_sp0 Q).  Local Notation SPB := (q_SPB Q).  Local Notation LR := (q_LR Q).    Local Notation B := (q_B Q).
  Local Notation LF := (q_LF Q).    Local Notation np0 := (q_np0 Q).  Local Notation BB := (q_BB Q).    Local Notation CH := (q_CH Q).
  Local Notation n := (q_n Q).      Local Notation p := (q_p Q).      Local Notation PB := (q_PB Q).    Local Notation len0 := (q_len0 Q).
  Local Notation dep := (q_dep Q).  Local Notation fw := (q_fw Q).    Local Notation lo := (q_lo Q).
  Local Notation SA := (q_SA Q).    Local Notation Fr := (q_Fr Q).
  Hypothesis PVL : pvl Q.
  Local Notation SP := (bv_unsigned sp).
  Local Notation POST := (pvalue_post AI TI ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F sp0 SPB LR B LF np0 BB CH n p PB len0 dep fw lo m g).
  Ltac lits := pose proof (pvl_lits Q PVL)
                 as ((PL1 & PL2 & PL3) & PB8 & AL & S47 & TOP & BOT & PB80 & CEIL & LO & TP & N1 & BLR & DEPN & DEP0 & PNZ
                     & CHOK & CHL & CHB & RA1 & RA2 & NPM & BBA & LEN0 & LFR & (GSA1 & GSA2) & (FAL & FLO & FHI & FNEW)
                     & SPR & RAR & S0R & (TOPR & BOTE) & CHN0);
               pose proof (Z.shiftr_div_pow2 Fr 3 ltac:(lia)) as SHFR; change (2^3) with 8 in SHFR;
               pose proof alloc_ceiling_eq as ACE; pose proof KHIGH_eqs as KHE.
  Ltac dj := cbn [disjoint_from cells_size Cells.csize Nat.add length map]; rewrite ?cells_size_mapC8, ?cells_size_mapC1, ?length_map; unfold AERRNO, ATP; lia.
  Hypothesis ENS : ensure_stmt AI TI.
  Hypothesis STRLEN : strlen_icpt_spec.
  Hypothesis REC : forall d, (d < n)%nat -> print_value_at AI TI d.
  Hypothesis FLAGLOW : art_flag_low_stmt AI.
  Hypothesis MEMSET : asan_memset_spec.


  Hypothesis PSTR : pstr_stmt AI TI.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma obj_val : forall (d : nat) c Bc,
    (d < n)%nat -> cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) ->
    OKATF Q 0x84248 c -> OKATF Q 0x841e8 c.
  Proof.
    intros d c Bc Dlt CHc CNZ SUB K. unfold OKATF, OST. intros until x31. intros CTXX OL. lits. bandM. sepM. unfold SHR, ASHBASE.
    pose proof CTXX as [CTX FRX]. (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelim (obj_loc9 Q loc LL OL) 3%nat; intros w0 w8 EL).
    unfold OKATF, OST in K. unfold SHR, ASHBASE in K.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. zstep. zstep. apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_rec Q PVL REC); [exact CTXX| exact Dlt| exact CHc| exact CNZ| exact SUB| lia| lia| rewrite unsigned_lit by lia; unfold AIMG_HI; lia]. }
    cbv beta. intros ms2 mo2 g2 PO.
    (nelim PO 25%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Fx' fcx' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x841f4)) with (Z_to_bv 64 0x841f4) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    eapply lscps_step_evt. cbv beta delta [mkR].
    destruct OUT as [(-> & EX) | (-> & buf2 & len2 & off2 & bs2 & CTX2 & NUL2)].
    { zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta. eapply (pv_ret0_2c8 Q PVL FLAGLOW); [exact EX| rewrite EL; reflexivity]. }
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 7%nat; intros HLb HPb PBSb _ _ PNb _). (nelimp FRXb 3%nat; intros _ LOCb _).
    (nelimp PNb 3%nat; intros PNb1 PNb2 PNb3).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXb)))))))))))) as SSZb.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) 4%nat; intros R1 R2 R3 R4). pose_perm_blk_band HLb HPb. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    rewrite EL in LOCb. cbn [map] in LOCb. unfold SHR, ASHBASE in LOCb. unfold PBS, wz in PBSb.
    (* [comment removed for export] *)
    zstep. pose proof (stack_shb0 m2 PB SSZb ltac:(lia)) as Z0. asan_chk Z0.
    zstep. zstep. zstep. if_cases Kb; zify_cond Kb; [exfalso; lia|]. clear Kb.
    pose proof (stack_shb0 m2 (PB + 16) SSZb ltac:(lia)) as Z16. asan_chk Z16.
    zstep. zstep. zstep. zstep.
    eapply evt_cut. { eapply (pvx_strlen_off Q PVL STRLEN); [exact CTX2| exact NUL2]. }
    cbv beta. intros ms' PO. clear Z0 Z16 PBSb LOCb SSZb.
    (nelim PO 21%nat; intros k u0' u1' u2' b1' b2' b3' b4' b5' b6' b7' u3' u4' u5' u6' m3 -> CTX3 K0 K1 KN).
    replace (ret_pc (Z_to_bv 64 0x84230)) with (Z_to_bv 64 0x84230) by (symmetry; apply ret_pc_even; [lia| reflexivity]). cbv beta delta [mkR].
    pose proof CTX3 as [CTXc FRXc]. (nelimp CTXc 9%nat; intros _ _ PBSc _ _ _ _ MIc _). (nelimp FRXc 3%nat; intros _ LOCc _).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
    rewrite EL in LOCc. cbn [map] in LOCc. unfold SHR, ASHBASE in LOCc. unfold PBS, wz in PBSc.
    pose proof (stack_shb0 m3 (PB + 16) SSZc ltac:(lia)) as Z16. asan_chk Z16.
    pose proof (munch_refl [(PB, PB + 32)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
    zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
    assert (CTX4 : PVX Q (dep + 1) m4 mo2 g2 LB2 TRS2 B2 np2 errv2 buf2 len2 (k + off2) bs2 loc jb SHP_IDLE Fx' fcx').
    { split.
      - eapply (pvm_off_store Q PVL); [exact CTXc| exact MU| exact WM| assumption| | lia].
        unfold PBS, wz. lazymatch goal with H : rw_cells asegs m4 PB _ |- _ => exact H end.
      - eapply (pvfr_wext Q PVL); [exact FRXc| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
    zstep. apply evt_done. cbv beta. eapply K; [exact CTX4| exact OL].
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma obj_sep : forall c nx pv ch ty p1 vs vi p2 vd ky,
    rw_cells asegs m c (node_cells nx pv ch ty p1 vs vi p2 vd ky) -> In (c, 64) B -> 0 <= nx < 2^64 ->
    (nx <> 0 -> OKAT Q 0x84010 nx) -> OKATF Q 0x84248 c.
  Proof.
    intros c nx pv ch ty p1 vs vi p2 vd ky ND CIN NXR K. unfold OKAT, OKATF, OST. intros until x31. intros CTXX OL. lits. bandM. sepM. unfold SHR, ASHBASE.
    assert (FZR : 0 <= Z.b2z (fz Q) <= 1) by (destruct (fz Q); cbn; lia).
    pose proof CTXX as [CTX FRX]. (nelimp CTX 7%nat; intros HL HP PBS1 _ _ PN _). (nelimp FRX 4%nat; intros _ LOC LL _).
    (nelimp PN 3%nat; intros PN1 PN2 PN3).
    pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTX)))))))))))) as SSZ.
    (nelim (obj_loc9 Q loc LL OL) 3%nat; intros w0 w8 EL). rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC.
    destruct (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTX ND CIN) as (NDm & SHc & (C1 & C2 & _ & C4) & CIN1).
    unfold node_cells, wz in NDm. unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in C1. bandM. sepM. try rewrite alloc_ceiling_eq in C4.
    unfold PBS, wz in PBS1.
    unfold OKAT, OST in K. unfold SHR, ASHBASE in K.
    (* [comment removed for export] *)
    set (NZ := Z.b2z (0 <? nx)). set (FM := Z.b2z (0 <? bv_unsigned (sx32 fw))).
    assert (NZ01 : 0 <= NZ <= 1) by (subst NZ; destruct (0 <? nx); cbn; lia).
    assert (FM01 : 0 <= FM <= 1) by (subst FM; destruct (0 <? bv_unsigned (sx32 fw)); cbn; lia).
    assert (FMfz : FM = 1 - Z.b2z (fz Q)).
    { subst FM. unfold fz. pose proof (bv_unsigned_in_range 64 (sx32 fw)).
      destruct (Z.ltb_spec 0 (bv_unsigned (sx32 fw))); destruct (Z.ltb_spec (bv_unsigned (sx32 fw)) 1); cbn; lia. }
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. pose proof (stack_shb0 mm (PB + 36) SSZ ltac:(lia)) as Z36. asan_chk Z36.
    zstep. zstep. asan_chk SHc.
    zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep.
    fold NZ. fold FM.
    apply evt_done. cbv beta.
    eapply lscps_bind.
    { eapply (pvx_ensure Q PVL ENS); [exact CTXX| lia| rewrite unsigned_lit by lia; lia]. }
    cbv beta. intros ms2 mo2 g2 PO. clear LOC PBS1 Z36 SSZ NDm SHc.
    (nelim PO 23%nat; intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m2 LB2 TRS2 B2 np2 errv2 -> OUT).
    replace (ret_pc (Z_to_bv 64 0x84290)) with (Z_to_bv 64 0x84290) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    destruct OUT as [(-> & EX) | (buf' & len' & bs' & -> & NZ' & CTX2 & ROOM & L31)].
    { eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. if_cases K0; zify_cond K0; [| exfalso; apply K0; reflexivity]. clear K0.
      apply evt_done. cbv beta. eapply (pv_ret0_2c8 Q PVL FLAGLOW); [exact EX| rewrite EL; reflexivity]. }
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ _ _ (proj1 (proj1 CTX2)) (perm_in_head _ _ _ (proj1 (proj2 (proj1 CTX2))))) 4%nat; intros R1 R2 R3 R4). unfold sclr, KHIGHMEM_BEG, AIMG_HI, KLOWSHADOW_BEG in R1. bandM. sepM. try rewrite alloc_ceiling_eq in R4.
    (* [comment removed for export] *)
    assert (JN2 : forall mq bsq x11q x12q x13q,
      PVX Q (dep + 1) mq mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off bsq loc jb SHP_IDLE Fx fcx ->
      LSCPS asegs POST
        (MS (mkR (Z_to_bv 64 0x84290) (Z_to_bv 64 SA) gp tp t0' t1' t2' sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf' + off + (NZ + FM))) x11q x12q x13q a4' a5' a6' a7'
                (Z_to_bv 64 (Z.shiftr (PB + 16) 3 + 2147450880)) (Z_to_bv 64 (NZ + FM)) (Z_to_bv 64 (PB + 24)) (Z_to_bv 64 (Z.shiftr (PB + 24) 3 + 2147450880)) (Z_to_bv 64 c) (Z_to_bv 64 PB) (Z_to_bv 64 (Z.shiftr c 3 + 2147450880))
                (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
            Fx (Z_to_bv 64 0x84300) fcx None mq (seg_rom asegs)) mo2 g2).
    { intros mq bsq x11q x12q x13q CTXq.
      pose proof CTXq as [CTXc FRXc]. (nelimp CTXc 9%nat; intros HLc HPc PBSc ARRc LENc PNc _ MIc _). (nelimp FRXc 3%nat; intros _ LOC _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLc (perm_in_head _ _ _ HPc)) as [_ SOB].
      pose proof (shadow_ok_shchk1 mq buf' len' (buf' + off + (NZ + FM)) SOB ltac:(lia)) as CKn.
      rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC.
      pose proof (munch_refl [(buf' + off + (NZ + FM), buf' + off + (NZ + FM) + 1)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. zstep. asan_chk CKn.
      ustore_at buf' off (buf' + off + (NZ + FM)) (NZ + FM) (wb 0) ltac:(reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      assert (CTX3 : PVX Q (dep + 1) m3 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd bsq (Z.to_nat (off + (NZ + FM))) (wb 0)) loc jb SHP_IDLE Fx fcx).
      { eapply (pvx_out_store Q PVL) with (W := [(buf' + off + (NZ + FM), buf' + off + (NZ + FM) + 1)]);
          [exact CTXq| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRc| rewrite upd_length; reflexivity]. }
      clear MU WM ARRc CTXq CTXc FRXc HLc PBSc SSZc SOB.
      pose proof CTX3 as [CTXd FRXd]. (nelimp CTXd 4%nat; intros _ _ PBSd _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXd)))))))))))) as SSZd.
      unfold PBS, wz in PBSd.
      pose proof (stack_shb0 m3 (PB + 16) SSZd ltac:(lia)) as Z16. asan_chk Z16.
      pose proof (munch_refl [(PB, PB + 32)] m3) as MU. pose proof (wmono_refl asegs m3) as WM.
      zstep. zstep. zstep. zstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m4 end.
      assert (CTX4 : PVX Q (dep + 1) m4 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' (off + (NZ + FM)) (upd bsq (Z.to_nat (off + (NZ + FM))) (wb 0)) loc jb SHP_IDLE Fx fcx).
      { split.
        - eapply (pvm_off_store Q PVL); [exact CTXd| exact MU| exact WM| assumption| | lia].
          unfold PBS, wz. lazymatch goal with H : rw_cells asegs m4 PB _ |- _ => exact H end.
        - eapply (pvfr_wext Q PVL); [exact FRXd| exact MU| exact WM|]. constructor; [unfold fr_wiv; cbn [fst snd]; lia| constructor]. }
      clear MU WM CTXd FRXd PBSd SSZd CTX3 Z16.
      (nelim (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (proj1 CTX4) ND CIN) 3%nat; intros NDd SHcd _).
      unfold node_cells, wz in NDd.
      asan_chk SHcd.
      zstep. zstep. zstep. zstep. zstep. if_cases Knx; zify_cond Knx.
      + apply evt_done. cbv beta. eapply (K ltac:(lia)); [exact CTX4| exact OL].
      + assert (E0 : nx = 0) by lia. rewrite E0 in *.
        zstep. apply evt_done. cbv beta. eapply (obj_close Q PVL ENS FLAGLOW); [exact CTX4| apply obj_locc_of; exact OL]. }
    (* [comment removed for export] *)
    assert (JN1 : forall mq bsq x11q x12q x13q,
      PVX Q (dep + 1) mq mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off bsq loc jb SHP_IDLE Fx fcx ->
      LSCPS asegs POST
        (MS (mkR (Z_to_bv 64 0x84290) (Z_to_bv 64 SA) gp tp t0' t1' t2' sp (Z_to_bv 64 SA) (Z_to_bv 64 (buf' + off + NZ)) x11q x12q x13q a4' a5' a6' a7'
                (Z_to_bv 64 (Z.shiftr (PB + 16) 3 + 2147450880)) (Z_to_bv 64 (NZ + FM)) (Z_to_bv 64 (PB + 24)) (Z_to_bv 64 (Z.shiftr (PB + 24) 3 + 2147450880)) (Z_to_bv 64 c) (Z_to_bv 64 PB) (Z_to_bv 64 (Z.shiftr c 3 + 2147450880))
                (Z_to_bv 64 (Z.shiftr Fr 3 + 2147450880)) (Z_to_bv 64 Fr) (Z_to_bv 64 2147450880) t3' t4' t5' t6')
            Fx (Z_to_bv 64 0x842c8) fcx None mq (seg_rom asegs)) mo2 g2).
    { intros mq bsq x11q x12q x13q CTXq.
      pose proof CTXq as [CTXc FRXc]. (nelimp CTXc 9%nat; intros HLc HPc PBSc ARRc LENc PNc _ MIc _). (nelimp FRXc 3%nat; intros _ LOC _).
      pose proof (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CTXc)))))))))))) as SSZc.
      destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLc (perm_in_head _ _ _ HPc)) as [_ SOB].
      rewrite EL in LOC. cbn [map] in LOC. unfold SHR, ASHBASE in LOC. unfold PBS, wz in PBSc.
      eapply lscps_step_evt. cbv beta delta [mkR].
      zstep. pose proof (stack_shb0 mq (PB + 36) SSZc ltac:(lia)) as Z36. asan_chk Z36.
      zstep. zstep. zstep. if_cases Kf; zify_cond Kf.
      - (* [comment removed for export] *)
        assert (EFM : FM = 0) by (subst FM; replace (0 <? bv_unsigned (sx32 fw)) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        apply evt_done. cbv beta. replace (buf' + off + NZ) with (buf' + off + (NZ + FM)) by lia. eapply JN2. exact CTXq.
      - assert (EFM : FM = 1) by (subst FM; replace (0 <? bv_unsigned (sx32 fw)) with true by (symmetry; apply Z.ltb_lt; pose proof (bv_unsigned_in_range 64 (sx32 fw)); lia); reflexivity).
        pose proof (shadow_ok_shchk1 mq buf' len' (buf' + off + NZ) SOB ltac:(lia)) as CKn.
        pose proof (munch_refl [(buf' + off + NZ, buf' + off + NZ + 1)] mq) as MU. pose proof (wmono_refl asegs mq) as WM.
        zstep. zstep. asan_chk CKn.
        zstep. zstep. ustore_at buf' off (buf' + off + NZ) NZ (wb 10) ltac:(reflexivity).
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
        assert (CTX3 : PVX Q (dep + 1) m3 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd bsq (Z.to_nat (off + NZ)) (wb 10)) loc jb SHP_IDLE Fx fcx).
        { eapply (pvx_out_store Q PVL) with (W := [(buf' + off + NZ, buf' + off + NZ + 1)]);
            [exact CTXq| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRc| rewrite upd_length; reflexivity]. }
        zstep. apply evt_done. cbv beta. replace (buf' + off + NZ + 1) with (buf' + off + (NZ + FM)) by lia. eapply JN2. exact CTX3. }
    (* [comment removed for export] *)
    pose proof CTX2 as [CTXb FRXb]. (nelimp CTXb 9%nat; intros HLb HPb PBSb ARRb LENb PNb _ MIb _).
    destruct (art_shadow AI _ _ _ _ _ _ _ _ _ _ _ HLb (perm_in_head _ _ _ HPb)) as [_ SOB].
    (nelim (arr_node_now Q PVL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ CTXb ND CIN) 3%nat; intros NDb SHcb _).
    unfold node_cells, wz in NDb.
    eapply lscps_step_evt. cbv beta delta [mkR].
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|]. clear K0.
    asan_chk SHcb.
    zstep. zstep. if_cases Knx; zify_cond Knx.
    - (* [comment removed for export] *)
      assert (ENZ : NZ = 0) by (subst NZ; replace (0 <? nx) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
      apply evt_done. cbv beta. replace (buf' + off) with (buf' + off + NZ) by lia. eapply JN1. exact CTX2.
    - (* [comment removed for export] *)
      assert (ENZ : NZ = 1) by (subst NZ; replace (0 <? nx) with true by (symmetry; apply Z.ltb_lt; lia); reflexivity).
      pose proof (shadow_ok_shchk1 m2 buf' len' (buf' + off) SOB ltac:(lia)) as CK0.
      pose proof (munch_refl [(buf' + off, buf' + off + 1)] m2) as MU. pose proof (wmono_refl asegs m2) as WM.
      zstep. zstep. asan_chk CK0.
      zstep. zstep. ustore_at buf' off (buf' + off) 0 (wb 44) ltac:(reflexivity).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) => rename mc into m3 end.
      assert (CTX3 : PVX Q (dep + 1) m3 mo2 g2 LB2 TRS2 B2 np2 errv2 buf' len' off (upd bs' (Z.to_nat (off + 0)) (wb 44)) loc jb SHP_IDLE Fx fcx).
      { eapply (pvx_out_store Q PVL) with (W := [(buf' + off, buf' + off + 1)]);
          [exact CTX2| exact MU| exact WM| assumption| constructor; [cbn [fst snd]; lia| constructor]| exact ARRb| rewrite upd_length; reflexivity]. }
      zstep. apply evt_done. cbv beta. replace (buf' + off + 1) with (buf' + off + NZ) by lia. eapply JN1. exact CTX3.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma obj_iter : forall (kk : nat) (d : nat) (c : Z) (Bc : list cblock),
    (length Bc <= kk)%nat -> (d < n)%nat -> cj_chain CJ_PRINTABLE m d c Bc -> c <> 0 -> (forall b, In b Bc -> In b B) -> OKAT Q 0x84010 c.
  Proof.
    induction kk as [|kk IH]; intros d c Bc LENB Dlt CHc CNZ SUB.
    { exfalso. pose proof (cj_chain_head_block _ _ _ _ _ CHc CNZ) as HIN. destruct Bc; [destruct HIN| cbn in LENB; lia]. }
    (nelim (cj_chain_cons_inv _ _ _ _ _ CHc CNZ) 24%nat; intros d0 nx pv ch ty p1 vs vi p2 vd ky Bv Bk Bcc Bn Ed ND TY _ SV SK CHC CHN EBc).
    (nelimp (cj_chain_ptr_range _ _ _ _ _ CHN) 3%nat; intros NX0 _ NX2).
    assert (CIN : In (c, 64) B) by (apply SUB; rewrite EBc; left; reflexivity).
    assert (SUBK : forall b, In b Bk -> In b B). { intros b Hb. apply SUB. rewrite EBc. right. rewrite !in_app_iff. right; left. exact Hb. }
    apply (obj_ind Q PVL ENS FLAGLOW).
    apply (obj_key Q PVL STRLEN FLAGLOW PSTR c nx pv ch ty p1 vs vi p2 vd ky Bk ND CIN SK SUBK).
    apply (obj_colon Q PVL ENS FLAGLOW).
    apply (obj_val d c Bc Dlt CHc CNZ SUB).
    apply (obj_sep c nx pv ch ty p1 vs vi p2 vd ky ND CIN ltac:(lia)).
    intros NXNZ. eapply (IH d nx Bn); [| lia| rewrite <- Ed in CHN; exact CHN| exact NXNZ|].
    - rewrite EBc in LENB. cbn in LENB. rewrite !length_app in LENB. lia.
    - intros b Hb. apply SUB. rewrite EBc. right. rewrite !in_app_iff. right; right; right. exact Hb.
  Qed.
End OBJC.


End CeilWrap.
(* [comment removed for export] *)
Ltac ustore_at B off ea e b tac :=
  lazymatch goal with
  | ARR : u8arr asegs ?m B ?buf |- _ =>
      let SOK := fresh "SOK" in let ARR' := fresh "ARR" in
      destruct (u8_store' m B buf ea (off + e) b ARR) as [SOK ARR'];
      [ lia | rewrite ?upd_length; lia
      | clear ARR; step;
        lazymatch goal with
        | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m1 ?a ?bs) _) =>
            replace (write_to_mem m1 a bs) with (write_to_mem m1 (wa ea) [b])
              by (f_equal; first [tac| unfold wa; f_equal; lia]);
            store_done; rename ARR' into ARR
        end ]
  end.
