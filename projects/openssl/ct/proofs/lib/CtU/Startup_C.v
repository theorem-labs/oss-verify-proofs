(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv Image.
From OSSVerify.Proofs.openssl.ct.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.openssl.ct.lib.P Require Import Str_tac InitMem Startup_glue Rnd.
From OSSVerify.Proofs.openssl.ct.lib.CtU Require Import F_memset F_memcpy Startup_B Startup_A.
From OSSVerify.openssl.ct.images Require Import Ubsan.
From OSSVerify.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m MUz :=
  lazymatch type of MUz with munch _ ?m _ =>
    lazymatch goal with WMz : wmono _ m _ |- _ => zidle_end MUz WMz end end.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.  (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac clear_big := repeat match goal with
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : u8arr _ _ _ _ |- _ => clear H
  | H : u32arr _ _ _ _ |- _ => clear H
  | H : u64arr _ _ _ _ |- _ => clear H
  | H : u8ro _ _ _ _ |- _ => clear H
  | H : stk _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  end.
Local Ltac tslia ::= first [ exact I | clear_big; first [ tlia | split; [ tlia | exact I ] ] ].

Notation ctusegs := ImageCt.ctusegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section InitLibc.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (R : Z) (g : word) (uid hw : word) (P : Z) (s : list byte)
            (pn0 pnf0 hw0 env0 : word) (gjunk : list byte).
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x333160); (0x333160, 0x353268);
                 (RGUARD, 0x353270); (RPROGNAME, 0x3534b8); (RLIBC, 0x353528)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  Definition init_libc_post : Z -> machine_state -> Prop :=
    fun tid ms' =>
      exists (x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg : word) (m' : word -> option byte),
        ms' = MS (mkR ra sp gp (Z_to_bv 64 RTP) x5 x6 x7 s0 s1 x10 x11 x12 x13 x14 x15 x16 x17
                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
                 F (ret_pc ra) fc None m' (seg_rom ctusegs)
        /\ munch W m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
        /\ stk ctusegs m' lo (bv_unsigned sp)
        /\ rw_cells ctusegs m' RTD
             (rtd_cells (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) (Z_to_bv 64 RTD) z64 (Z_to_bv 64 tid) z64 (Z_to_bv 64 2)
                        (Z_to_bv 64 (RTD + 120)) (Z_to_bv 64 (RLIBC + 56)) (guard_of g) (Z_to_bv 64 (RTD + 216)) z64)
        /\ rw_cells ctusegs m' RLIBC
             (libc_cells (Z_to_bv 8 1) (Z_to_bv 64 AUXV) (Z_to_bv 64 224) (Z_to_bv 64 8) (Z_to_bv 64 4096))
        /\ rw_cells ctusegs m' RHWCAP [C8 hw]
        /\ rw_cells ctusegs m' RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)]
        /\ rw_cells ctusegs m' RGUARD [C8 (guard_of g)]
        /\ rw_cells ctusegs m' RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 (Z_to_bv 64 8); C8 z64]
        /\ rw_cells ctusegs m' RENVIRON [C8 (Z_to_bv 64 E)]
        /\ rw_cells ctusegs m' RSYSINFO [C8 z64]
        /\ rw_cells ctusegs m' RDEFSTACK [C4 (Z_to_bv 64 0x20000)]
        /\ rw_cells ctusegs m' RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x3534b0); C8 (Z_to_bv 64 RPROGNAME)]
        /\ rw_cells ctusegs m' RGOT_SSP [C8 (Z_to_bv 64 RGUARD)]
        /\ rw_cells ctusegs m' RGOT_DYNAMIC [C8 z64]
        /\ bytes_at ctusegs m' E (u64s eps ++ le8 z64 ++ u64s (auxv20 (Z_to_bv 64 R) uid hw))
        /\ bytes_at ctusegs m' P (s ++ [Z_to_bv 8 0])
        /\ bytes_at ctusegs m' R (le8 g)
        /\ (0 < tid < 4194304)%Z.

  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x355000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition pn_post (x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 : word) (m0 : word -> option byte)
      : machine_state -> Prop :=
    fun ms => exists (pg : word) (mm : word -> option byte),
      ms = MS (mkR (Z_to_bv 64 0x2b25c0) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
                   (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + Z.of_nat (length s) + 1)) (Z_to_bv 64 47)
                   z64 x14 x15 x16 x17 (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
              F (Z_to_bv 64 0x2b269c) fc None mm (seg_rom ctusegs)
      /\ munch [(RPROGNAME, 0x3534b0)]%Z m0 mm /\ wmono ctusegs m0 mm /\ mem_inv ctusegs mm
      /\ rw_cells ctusegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)].

  Lemma pn_loop : forall (k : nat) (j : Z) (m0 mm : word -> option byte) x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg,
    (Z.of_nat k = Z.of_nat (length s) + 1 - j)%Z -> (1 <= j)%Z ->
    munch [(RPROGNAME, 0x3534b0)]%Z m0 mm -> wmono ctusegs m0 mm -> mem_inv ctusegs mm ->
    bytes_at ctusegs mm P (s ++ [Z_to_bv 8 0]) ->
    rw_cells ctusegs mm RPROGNAME [C8 pg; C8 (Z_to_bv 64 P)] ->
    evt ctusegs (pn_post x5 x6 x7 x9 x11 x14 x15 x16 x17 x28 x29 x30 x31 m0)
      (MS (mkR (Z_to_bv 64 0x2b25c0) (Z_to_bv 64 (bv_unsigned sp + -384)) gp x11 x5 x6 x7
               (Z_to_bv 64 P) x9 (Z_to_bv 64 RPROGNAME) (Z_to_bv 64 (P + j)) (Z_to_bv 64 47) x13 x14 x15 x16 x17
               (Z_to_bv 64 RLIBC) s3 s4 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
          F (Z_to_bv 64 0x2b2690) fc None mm (seg_rom ctusegs)).
  Proof.
    induction k as [|k IHk];
      intros j m0 mm x5 x6 x7 x9 x11 x13 x14 x15 x16 x17 x28 x29 x30 x31 pg CNT JPOS FOOT GROW INV STR PNC;
      cycle 1.
    - assert (INNER : (Z.to_nat (j - 1) < length s)%nat) by lia.
      destruct (nth_error s (Z.to_nat (j - 1))) as [b|] eqn:AT;
        [| apply nth_error_None in AT; lia].
      pose proof (proj1 (Forall_forall _ _) NONUL b (nth_error_In _ _ AT)) as BNZ. cbn beta in BNZ.
      assert (ATS : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some b)
        by (rewrite nth_error_app1 by exact INNER; exact AT).
      pose proof (u8ro_read ctusegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR ATS ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RDB.
      pose proof (byte_range b) as BR.
      assert (WIDE : bv_unsigned (Z_to_bv 64 (bv_unsigned b)) = bv_unsigned b) by (apply unsigned_lit; lia).
      lstep. lstep.
      destruct (Z.eq_dec (bv_unsigned b) 47) as [SLASH|PLAIN].
      + if_true. lstep. lstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        apply (IHk (j + 1)%Z m0 m1 x5 x6 x7 x9 x11 (Z_to_bv 64 (bv_unsigned b)) x14 x15 x16 x17 x28 x29 x30 x31
                   (Z_to_bv 64 (P + j)%Z)); [lia | lia | exact FOOT | exact GROW | exact INV | exact STR | exact PNC].
      + if_false. astep. lstep.
        replace (P + j + 1)%Z with (P + (j + 1))%Z by lia.
        apply (IHk (j + 1)%Z m0 mm x5 x6 x7 x9 x11 (Z_to_bv 64 (bv_unsigned b)) x14 x15 x16 x17 x28 x29 x30 x31 pg);
          [lia | lia | exact FOOT | exact GROW | exact INV | exact STR | exact PNC].
    - assert (LAST : nth_error (s ++ [Z_to_bv 8 0]) (Z.to_nat (j - 1)) = Some (Z_to_bv 8 0)).
      { rewrite nth_error_app2 by lia. replace (Z.to_nat (j - 1) - length s)%nat with O by lia. reflexivity. }
      pose proof (u8ro_read ctusegs mm P _ (j - 1) _ (Z_to_bv 64 (P + j + -1)) STR LAST ltac:(lia)
                    ltac:(unfold wa; f_equal; lia)) as RDB.
      lstep. astep. astep.
      replace (P + j)%Z with (P + Z.of_nat (length s) + 1)%Z by lia.
      finish2. exact PNC.
  Qed.

  (* [comment removed for export] *)
  Ltac scan_it AUXB vi ki :=
    lstep; if_false; ldaux AUXB vi; lstep; lstep;
    (try lazymatch goal with |- context [Z_to_bv 64 (bv_unsigned ?spv + -336 + ?c)] =>
      let off := eval vm_compute in (-336 + c)%Z in
      replace (Z_to_bv 64 (bv_unsigned spv + -336 + c)) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    (try lazymatch goal with |- context [Z_to_bv 64 (?c + (bv_unsigned ?spv + -336))] =>
      let off := eval vm_compute in (c + -336)%Z in
      replace (Z_to_bv 64 (c + (bv_unsigned spv + -336))) with (Z_to_bv 64 (bv_unsigned spv + off)) by (f_equal; lia)
    end);
    lstep; lstep; ldaux AUXB ki; lstep; astep.

  Lemma init_libc_spec : forall tp a0 a1,
    stk ctusegs m lo (bv_unsigned sp) ->
    bytes_at ctusegs m E (u64s eps ++ le8 z64 ++ u64s (auxv20 (Z_to_bv 64 R) uid hw)) ->
    bytes_at ctusegs m P (s ++ [Z_to_bv 8 0]) ->
    bytes_at ctusegs m R (le8 g) ->
    rw_cells ctusegs m RPROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells ctusegs m RHWCAP [C8 hw0] ->
    rw_cells ctusegs m RENVIRON [C8 env0] ->
    rw_cells ctusegs m RSYSINFO [C8 z64] ->
    rw_cells ctusegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
    rw_cells ctusegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells ctusegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
    rw_cells ctusegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells ctusegs m RGUARD [CB 8 gjunk] ->
    rw_cells ctusegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x3534b0); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells ctusegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
    rw_cells ctusegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv ctusegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl ctusegs (at_node ctusegs) (enode NSetTid dec_set_tid) (epost init_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x2b2594) fc None m (seg_rom ctusegs)).
  Proof.
    intros tp a0 a1 STK ENVB PNB RNDB PNC HWC ENVC SYSC LIBC TDC TLLC DSTK GRDC GOT3C GSSPC GDYNC MINV ARG0 ARG1.
    subst a0 a1.
    unfold libc_cells, td_cells in *.
    pose proof (munch_refl W m) as FOOT.
    pose proof (wmono_refl ctusegs m) as GROW.
    pose proof (bv_unsigned_in_range 64 sp) as SPRNG. unfold bv_modulus in SPRNG. cbn in SPRNG.
    pose proof (bytes_at_bound _ _ _ _ ENVB) as ENVRNG.
    pose proof (bytes_at_bound _ _ _ _ PNB) as PNRNG.
    pose proof (bytes_at_bound _ _ _ _ RNDB) as RNDRNG.
    rewrite !length_app, u64s_length, length_le8 in ENVRNG.
    rewrite length_app in PNRNG. rewrite length_le8 in RNDRNG. cbn [length] in PNRNG.
    iprefix.
    carve_frame 384%nat STK.
    do 11 lstep.
    lazymatch type of FR with rw_cells ?sg ?mc ?A ?cs => split_for_access FR sg mc A cs 48%nat 304%nat end.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRLO FR].
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUXA FRHI].
    literal_cell_sizes_in AUXA. literal_cell_sizes_in FRHI.
    replace (bv_unsigned sp + -384 + Z.of_nat 48)%Z with (bv_unsigned sp + -336)%Z in AUXA, FRHI by lia.
    replace (bv_unsigned sp + -336 + Z.of_nat 304)%Z with (bv_unsigned sp + -32)%Z in FRHI by lia.
    call (memset_specZ (bv_unsigned sp + -336) 304 0);
      [exact AUXA | exact MINV | reflexivity | reflexivity | reflexivity | lia | lia | lia | ].
    rename POST into AUXA. change (Z.to_nat 304) with 304%nat in AUXA.
    do 3 lstep.
    eapply (envp_count_loop eps); [exact EPS | exact ENVB | ].
    pose proof (proj2 (proj1 (bytes_at_app _ _ _ _ _) ENVB)) as AUXB.
    apply (proj1 (bytes_at_app _ _ _ _ _)) in AUXB. destruct AUXB as [_ AUXB].
    rewrite u64s_length, length_le8 in AUXB.
    replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
    do 3 lstep. ldaux AUXB 0%nat. astep. do 4 lstep.
    scan_it AUXB 1%nat 2%nat. scan_it AUXB 3%nat 4%nat. scan_it AUXB 5%nat 6%nat.
    scan_it AUXB 7%nat 8%nat. scan_it AUXB 9%nat 10%nat. scan_it AUXB 11%nat 12%nat.
    scan_it AUXB 13%nat 14%nat. scan_it AUXB 15%nat 16%nat. scan_it AUXB 17%nat 18%nat.
    assert (PNZ : negb (bv_eqb (Z_to_bv 64 P) z64) = true).
    { unfold bv_eqb. rewrite !unsigned_lit by lia. apply negb_true_iff, Z.eqb_neq. lia. }
    steps_to 0x2b2650%Z. lstep. rewrite PNZ; cbv iota. lstep. rewrite PNZ; cbv iota.
    steps_to 0x2b2690%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
      call (pn_loop (length s) 1%Z mc mc);
        [lia | lia | apply munch_refl | apply wmono_refl | exact MI | exact PNB | exact PNC | ] end.
    rename POST into PNC.
    do 2 lstep.
    pose proof (proj2 (proj1 (rw_cells_app _ _ _ [_] _) AUXA)) as AUX3.
    apply (proj1 (rw_cells_app _ _ _ [_; _; _] _)) in AUX3. destruct AUX3 as [AUX3 _].
    literal_cell_sizes_in AUX3.
    replace (bv_unsigned sp + -336 + Z.of_nat 24)%Z with (bv_unsigned sp + -312)%Z in AUX3 by lia.
    name_sp sp (-384)%Z.
    icallk (init_tls_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              lo z64 (Z_to_bv 64 4096) (Z_to_bv 64 AUXV)).
    all: lazymatch goal with
         | |- forall _, _ => idtac
         | |- stk _ _ _ _ => rewrite Hsp; exact STK
         | |- rw_cells _ _ (bv_unsigned ?a0v + 24) _ =>
             replace (bv_unsigned a0v + 24)%Z with (bv_unsigned sp + -312)%Z; [exact AUX3 | rewrite unsigned_lit by lia; lia]
         | |- rw_cells _ _ _ _ => hyp_by_addr
         | |- mem_inv _ _ => exact MI0
         | |- _ => rewrite ?Hsp, ?unsigned_lit by lia; lia
         end.
    ipost ctusegs. unname_sp. unfold libc_cells in *.
    do 2 lstep.
    name_sp sp (-384)%Z.
    call (init_ssp_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo R g).
    all: lazymatch goal with
         | |- evt _ _ _ => idtac
         | |- stk _ _ _ _ => rewrite Hsp; match goal with ST : stk _ _ _ _ |- _ => exact ST end
         | |- rw_cells _ _ _ _ => hyp_by_addr
         | |- bytes_at _ _ _ _ => hyp_by_addr
         | |- mem_inv _ _ => hyp_by_addr
         | |- _ = _ => reflexivity
         | |- _ => rewrite ?Hsp; lia
         end.
    unname_sp.
    steps_to 0x2b27a8%Z.
    do 6 lstep.
    match goal with ST0 : stk _ _ _ _ |- _ => rename ST0 into STK end.
    release_frame FRLO STK (bv_unsigned sp + -336)%Z.
    release_frame AUXA STK (bv_unsigned sp + -32)%Z.
    release_frame FRHI STK (bv_unsigned sp).
    sys_finish.
    all: hyp_by_addr.
  Qed.
End InitLibc.
