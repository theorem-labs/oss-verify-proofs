(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: ported to LPS 727298f3 (rinit_libc_spec walks the launch's auxv (rauxv: 27 or 29 pairs by CONFIG_RSEQ) in place of rauxv20, skipping the keys 38 and above, and hands off at the auxv loop's exit). *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Arr Bytes ITree Nodes Decode SysStep RegsEquiv.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import STRW_tac InitMem.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import R_StartupLib R_StartupLib.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import RF_memset RF_memcpy R_Startup_A.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Images.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Import PortShim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.  (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Import ITree.Exc.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.R Require Export R_Startup_B1.

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Section RInitLibc.
  Variables (ra sp gp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (lo : Z)
            (E : Z) (eps : list word) (R : Z) (P : Z) (s : list byte)
            (pn0 pnf0 hw0 env0 : word) (gjunk : list byte) (uid hw : word) (b0 b1 b2 b3 b4 b5 b6 b7 : byte)
            (la : LaunchAuxv) (ent gid efn : word).
  Let rb : list byte := [b0; b1; b2; b3; b4; b5; b6; b7].
  Hypothesis GRD : rc_guard = guard_of rb.
  Notation W := [(bv_unsigned sp - 448, bv_unsigned sp); (RENVIRON, 0x54d48); (0x54d50, 0x54d80);
                 (RGUARD, 0x54fb8); (RPROGNAME, 0x54fd0); (RLIBC, 0x55040)]%Z.
  Notation AUXV := (E + 8 * (Z.of_nat (length eps) + 1))%Z.

  (* [comment removed for export] *)
  Local Notation rinit_libc_post := (R_Startup_B1.rinit_libc_post ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo E eps R P s uid hw b0 b1 b2 b3 b4 b5 b6 b7 la ent gid efn).
  Hypothesis EPS : Forall (fun w : word => bv_unsigned w <> 0%Z) eps.
  Hypothesis NONUL : Forall (fun b : byte => bv_unsigned b <> 0%Z) s.
  Hypothesis LO : (lo <= bv_unsigned sp - 448)%Z.
  Hypothesis LOLO : (0x56000 <= lo)%Z.
  Hypothesis SPE : (bv_unsigned sp <= E)%Z.
  Hypothesis SPP : (bv_unsigned sp <= P)%Z.
  Hypothesis SPR : (bv_unsigned sp <= R)%Z.
  Local Notation rinit_libc_from_16db8 :=
    (R_Startup_B1.rinit_libc_from_16db8 ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo E eps R P s pn0 pnf0 hw0 gjunk uid hw b0 b1 b2 b3 b4 b5 b6 b7 la ent gid efn GRD NONUL LO LOLO SPE SPP SPR).

  Ltac rscan_it AUXB vi ki :=
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
  (* LPS 08b1429: a pair whose key is 38 or more (the cache-geometry keys, AT_MINSIGSTKSZ) is
     skipped: 0x16da0's [bltu] is taken back to the key load at 0x16d94. *)
  Ltac rscan_skip AUXB ki := lstep; if_true; ldaux AUXB ki; lstep; astep.

  Lemma rinit_libc_spec : forall tp a0 a1,
    stk rsegs m lo (bv_unsigned sp) ->
    bytes_at rsegs m E (u64s eps ++ le8 z64 ++ u64s (rauxv la ent uid gid hw (Z_to_bv 64 R) efn)) ->
    bytes_at rsegs m P (s ++ [Z_to_bv 8 0]) ->
    bytes_at rsegs m R rb ->
    rw_cells rsegs m RPROGNAME [C8 pn0; C8 pnf0] ->
    rw_cells rsegs m RHWCAP [C8 hw0] ->
    rw_cells rsegs m RENVIRON [C8 env0] ->
    rw_cells rsegs m RSYSINFO [C8 z64] ->
    rw_cells rsegs m RLIBC (libc_cells (Z_to_bv 8 0) z64 z64 z64 z64) ->
    rw_cells rsegs m RTD (td_cells z64 z64 z64 z64 z64 z64 z64 z64 z64 z64 z64) ->
    rw_cells rsegs m RTLL [C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64; C8 z64] ->
    rw_cells rsegs m RDEFSTACK [C4 (Z_to_bv 64 0x20000)] ->
    rw_cells rsegs m RGUARD [CB 8 gjunk] ->
    rw_cells rsegs m RGOT3 [C8 (Z_to_bv 64 RENVIRON); C8 (Z_to_bv 64 0x54fc8); C8 (Z_to_bv 64 RPROGNAME)] ->
    rw_cells rsegs m RGOT_SSP [C8 (Z_to_bv 64 RGUARD)] ->
    rw_cells rsegs m RGOT_DYNAMIC [C8 z64] ->
    mem_inv rsegs m ->
    a0 = Z_to_bv 64 E -> a1 = Z_to_bv 64 P ->
    impl rsegs (at_node rsegs) (enode NSetTid dec_set_tid) (epost rinit_libc_post)
         (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x16d2c) fc None m (seg_rom rsegs)).
  Proof.
    intros tp a0 a1 ST ENV STR RND G2 HW ENVC SI LC TDC MT DS GU GOT3 GG GD MI -> ->.
    unfold td_cells, libc_cells in *.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl rsegs m) as WM.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    pose proof (bytes_at_bound _ _ _ _ ENV) as EB. rewrite !app_length, !u64s_length, length_le8, rauxv_length in EB.
    pose proof (bytes_at_bound _ _ _ _ STR) as PB. rewrite app_length in PB. cbn [length] in PB.
    pose proof (bytes_at_bound _ _ _ _ RND) as RB. unfold rb in RB. cbn [length] in RB.
    iprefix.
    carve_frame 384%nat ST.
    do 10 lstep.
    (* [comment removed for export] *)
    apply (rw_cells_split_CB rsegs _ _ [] 352 _ _ [48; 304]%nat) in FR; [|reflexivity]. cbn [mk_CB_cells app] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [FRlo FR]. cbn [cells_size csize Nat.add] in FR.
    apply (proj1 (rw_cells_app _ _ _ [_] _)) in FR. destruct FR as [AUX FRhi]. cbn [cells_size csize Nat.add] in FRhi.
    change (Z.of_nat 48) with 48%Z in *. change (Z.of_nat 304) with 304%Z in *.
    replace (bv_unsigned sp + -384 + 48)%Z with (bv_unsigned sp + -336)%Z in AUX by lia.
    replace (bv_unsigned sp + -384 + 48 + 304)%Z with (bv_unsigned sp + -32)%Z in FRhi by lia.
    lstep. call (rmemset_specZ (bv_unsigned sp + -336) 304 0); [exact AUX | exact MI | reflexivity | reflexivity | reflexivity | lia | lia | lia |].
    rename POST into AUX. change (Z.to_nat 304) with 304%nat in AUX. try rename MI0 into MI.
    apply (rw_cells_recast rsegs _ _ _ (repeat (C8 z64) 38)) in AUX;
      [| cbn; repeat split; exact I | vm_compute; reflexivity | reflexivity]. cbn [repeat] in AUX.
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    eapply (renvp_count_loop eps); [exact EPS | exact ENV |].
    (* [comment removed for export] *)
    lstep. lstep. lstep.
    pose proof ENV as AUXB. apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB].
    apply bytes_at_app in AUXB. destruct AUXB as [_ AUXB]. rewrite u64s_length, length_le8 in AUXB.
    replace (E + Z.of_nat (8 * length eps) + Z.of_nat 8)%Z with AUXV in AUXB by lia.
    pose proof AUXB as AUXB0.
    unfold rauxv, auxv_entries, AT_NULL, AT_PHDR, AT_PHENT, AT_PHNUM, AT_PAGESZ, AT_BASE, AT_FLAGS, AT_ENTRY,
      AT_UID, AT_EUID, AT_GID, AT_EGID, AT_HWCAP, AT_CLKTCK, AT_SECURE, AT_RANDOM, AT_RSEQ_FEATURE_SIZE,
      AT_RSEQ_ALIGN, AT_EXECFN, AT_SYSINFO_EHDR, AT_L1I_CACHESIZE, AT_L1I_CACHEGEOMETRY, AT_L1D_CACHESIZE,
      AT_L1D_CACHEGEOMETRY, AT_L2_CACHESIZE, AT_L2_CACHEGEOMETRY, AT_L3_CACHESIZE, AT_L3_CACHEGEOMETRY,
      AT_MINSIGSTKSZ in AUXB.
    cbn [flat_map app fst snd] in AUXB.
    (* LPS 08b1429: the auxv is 26 pairs, the two CONFIG_RSEQ pairs when [la_rseq la], then
       AT_NULL ([StackLayout.auxv_entries]); both layouts are walked. *)
    ldaux AUXB 0%nat. lstep. if_false. lstep. lstep. lstep. lstep.
    rscan_it AUXB 1%nat 2%nat.
    rscan_skip AUXB 4%nat. rscan_skip AUXB 6%nat. rscan_skip AUXB 8%nat. rscan_skip AUXB 10%nat.
    rscan_skip AUXB 12%nat. rscan_skip AUXB 14%nat. rscan_skip AUXB 16%nat. rscan_skip AUXB 18%nat.
    rscan_skip AUXB 20%nat.
    rscan_it AUXB 21%nat 22%nat. rscan_it AUXB 23%nat 24%nat. rscan_it AUXB 25%nat 26%nat. rscan_it AUXB 27%nat 28%nat.
    rscan_it AUXB 29%nat 30%nat. rscan_it AUXB 31%nat 32%nat. rscan_it AUXB 33%nat 34%nat. rscan_it AUXB 35%nat 36%nat.
    rscan_it AUXB 37%nat 38%nat. rscan_it AUXB 39%nat 40%nat. rscan_it AUXB 41%nat 42%nat. rscan_it AUXB 43%nat 44%nat.
    rscan_it AUXB 45%nat 46%nat. rscan_it AUXB 47%nat 48%nat. rscan_it AUXB 49%nat 50%nat.
    (* [destruct] already rewrites [la_rseq la] in the hypotheses; the copy is normalized. *)
    destruct (la_rseq la) eqn:Ers;
      pose proof AUXB as AUXB'; try rewrite Ers in AUXB'; cbn [flat_map app fst snd] in AUXB'.
    - rscan_it AUXB' 51%nat 52%nat. rscan_it AUXB' 53%nat 54%nat. rscan_it AUXB' 55%nat 56%nat.
      eapply (rinit_libc_from_16db8 _ _ []); try eassumption; rewrite ?Ers in *; cbn [auxv_count] in *; lia.
    - rscan_it AUXB' 51%nat 52%nat.
      eapply (rinit_libc_from_16db8 _ _ [] _ _ _ _ _ _ _ _ _ _ _ _ _ _ z64 z64); try eassumption;
        rewrite ?Ers in *; cbn [auxv_count] in *; lia.
  Qed.
End RInitLibc.
End RC__1.
