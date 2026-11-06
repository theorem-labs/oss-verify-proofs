(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/bzip2/bzip2_compress_target/lib/K/A/I_amemcpy.v, with its module paths and addresses changed; 66 of its 188 lines of code are new or changed and 17 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-10: moved from image B (fuzz_preset.asan-ubsan f8f98a95), commit 3244f5c71f6, to the #102 pin B' (fuzz_preset.asan-ubsan d663f82d, unstripped c90d4fa5): 6 address numerals by the frozen alreloc (sha256 c4338d099cfb8025, commit d99acc3edd9, same-unit move, --assume-source), each by symbol + offset in both images, or for a .rodata string by its unique content in both; GXA keys and history lines kept (report and decisions: the relocation record, the internal file resolve-B-why.tsv). *)
(* Modified by Theorem Labs, 2026-10: relocated onto omx-clap-core/fuzz_preset.asan-ubsan (image B, f8f98a95) from commit 3e35620c52e proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_amemcpy.v: module paths (lib/A/Bz -> lib/AU/PSnpBz) and the address numerals by alreloc (sha256 c4338d099cfb8025, commit d99acc3edd97, --build asan-ubsan --from-build asan), each by symbol + offset in both images (per-numeral report: the relocation record, B-run). *)
(* Ported by the runtime port from commit affce6489c8 proofs/omx-clap-core/fuzz_manifest/lib/A/Bz/A/I_amemcpy.v, unchanged. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.Lib Require Import StoreFast.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU.PSnpBz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck D_kit
  I_memcpyw I_amemcpyw I_amemcpyw2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Import ListNotations.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Definition amemcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (d s : Z) (src : list byte) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 d) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(d, d + Z.of_nat (length src)); (bv_unsigned sp - AMEMCPY_DEPTH, bv_unsigned sp)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ rw_cells asegs m' d [CB (length src) src] /\ bytes_at asegs m' s src.

Definition memcpy_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (a0 a1 a2 : word) (src : list byte) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1' a2' a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1' a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(bv_unsigned a0, bv_unsigned a0 + bv_unsigned a2)]%Z m m' /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ rw_cells asegs m' (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) src]
    /\ bytes_at asegs m' (bv_unsigned a1) src.

Definition memcpy_stmt : Prop :=
  forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (src junk : list byte),
  bytes_at asegs m (bv_unsigned a1) src ->
  length src = Z.to_nat (bv_unsigned a2) ->
  rw_cells asegs m (bv_unsigned a0) [CB (Z.to_nat (bv_unsigned a2)) junk] ->
  (bv_unsigned a0 = bv_unsigned a1 \/ bv_unsigned a1 + bv_unsigned a2 <= bv_unsigned a0 \/ bv_unsigned a0 + bv_unsigned a2 <= bv_unsigned a1)%Z ->
  (bv_unsigned a0 + bv_unsigned a2 <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (memcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc a0 a1 a2 src m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x9bb04) fc None m (seg_rom asegs)).

Lemma stk_after_copy : forall m m' lo hi a n (bs : list byte),
  stk asegs m lo hi -> munch [(a, a + n)] m m' -> wmono asegs m m' ->
  rw_cells asegs m' a [CB (Z.to_nat n) bs] -> stk asegs m' lo hi.
Proof.
  intros m m' lo hi a n bs (H0 & H1 & H) MU WM ((Hwf & B0 & B1 & B) & _).
  split; [exact H0|]. split; [exact H1|]. intros x Hx.
  destruct (H x Hx) as [Hw (b & Hb)]. split; [exact (WM _ Hw)|].
  assert (Ex : bv_unsigned (wa x) = x) by (apply wa_unsigned; lia).
  cbn [cells_bytes cbytes cells_wf cell_wf] in Hwf, B0, B1, B. rewrite app_nil_r in B1, B. destruct Hwf as [Hl _].
  destruct (Z_lt_le_dec x a) as [L|L]; [| destruct (Z_lt_le_dec x (a + n)) as [L2|L2]].
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite Ex. cbn [outside]. split; [lia| exact I].
  - assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
    specialize (B (Z.to_nat (x - a)) Hi). rewrite Z2Nat.id in B by lia. replace (a + (x - a)) with x in B by lia.
    destruct (nth_error bs (Z.to_nat (x - a))) as [c|] eqn:E; [exists c; exact B|].
    apply nth_error_None in E. lia.
  - exists b. unfold mrd in *. rewrite (MU (wa x)); [exact Hb|]. rewrite Ex. cbn [outside]. split; [lia| exact I].
Qed.

Section WithRIP.
Hypothesis RIP : rip_stmt.
Hypothesis MC : memcpy_stmt.

Theorem amemcpy_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (d s : Z) (src junk : list byte) (lo : Z),
  a0 = Z_to_bv 64 d -> a1 = Z_to_bv 64 s -> a2 = Z_to_bv 64 (Z.of_nat (length src)) ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - AMEMCPY_DEPTH -> kHighShadowEnd < lo -> bv_unsigned sp < 2^63 ->
  0 <= d -> 0 <= s -> d + Z.of_nat (length src) <= 2^47 -> s + Z.of_nat (length src) <= 2^47 ->
  (d = s \/ d + Z.of_nat (length src) <= s \/ s + Z.of_nat (length src) <= d) ->
  (Z.of_nat (length src) = 0 \/ s + Z.of_nat (length src) <= bv_unsigned sp - AMEMCPY_DEPTH \/ bv_unsigned sp <= s) ->
  (Z.of_nat (length src) = 0 \/ d + Z.of_nat (length src) <= bv_unsigned sp - AMEMCPY_DEPTH \/ bv_unsigned sp <= d) ->
  bytes_at asegs m s src -> rw_cells asegs m d [CB (length src) junk] ->
  chk_ok m s (Z.of_nat (length src)) -> chk_ok m d (Z.of_nat (length src)) -> m2s_cells m -> icells m -> mem_inv asegs m ->
  evt asegs (amemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc d s src lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x524d0) fc None m (seg_rom asegs)).
Proof using RIP MC.
  intros until lo. intros -> -> -> ST LO LOLO SPH D0 S0 DH SH OV SEPS SEPD SRC DST CS CD M2S IC MI.
  unfold kHighShadowEnd in *.
  set (n := Z.of_nat (length src)) in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  pose proof (munch_refl [(d, d + n); (usp - 2224, usp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  pose proof (munch_refl [(usp - 2224, usp)] m) as MUf.
  pose proof IC as (G2 & G1 & RM & SHC & RI).
  assert (SRC0 : keep (bytes_at asegs m s src)) by exact SRC. clear SRC.
  assert (DST0 : keep (rw_cells asegs m d [CB (length src) junk])) by exact DST. clear DST.
  assert (N0 : 0 <= n) by lia.
  assert (RS : n = 0 \/ s + n <= 0x7fff8000 \/ 0x10007fff8000 <= s).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CS as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  assert (RD : n = 0 \/ d + n <= 0x7fff8000 \/ 0x10007fff8000 <= d).
  { destruct (Z.eq_dec n 0) as [E|NE]; [left; exact E| right]. destruct CD as (_ & _ & RO). destruct (RO ltac:(lia)) as (RIM & _).
    unfold region_in_mem, kLowMemEnd, kHighShadowEnd, kHighMemEnd in RIM. lia. }
  (* [comment removed for export] *)
  assert (OFF : forall p, chk_ok m p n -> 0 <= p -> p + n <= 2^47 ->
            forall m', munch [(d, d + n); (usp - 2224, usp)] m m' -> chk_ok m' p n).
  { intros p CP P0 P1 m' MU'. apply (chk_ok_agree m m' p n CP P0 P1). apply (agree_of_munch _ _ _ _ MU'). intros x Hx.
    cbn [outside]. split; [lia| split; [lia| exact I]]. }
  call (amemcpy_prologue usp d s n); [exact ST| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia| exact OV
        | exact IC| exact MI|].
  rename PC into FRs. rename PC0 into FR. rename POST into ST1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (OFF s CS S0 SH mm MU) as CS1; pose proof (OFF d CD D0 DH mm MU) as CD1 end.
  assert (IC1 : icells x) by (split; [exact G2| split; [exact G1| split; [exact RM| split; [exact SHC| exact RI]]]]).
  assert (M2S1 : m2s_cells x).
  { destruct M2S as (M1 & M2 & M3). split; [| split].
    - apply (rw_cells_agree asegs m x _ _ M1); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia.
    - apply (rw_cells_agree asegs m x _ _ M2); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia.
    - apply (rw_cells_agree asegs m x _ _ M3); [| exact WM]. apply (agree_of_munch _ _ _ _ MUf). intros y Hy. cbn in Hy |- *. lia. }
  call (amemcpy_src RIP usp d s n); [exact ST1| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
        | exact CS1| exact M2S1| exact IC1| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST2 end.
  clear CS1 CD1 IC1 M2S1.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (OFF d CD D0 DH mm MU) as CD2;
    assert (IC2 : icells mm) by (split; [exact G2| split; [exact G1| split; [exact RM| split; [exact SHC| exact RI]]]]);
    assert (M2S2 : m2s_cells mm) by (destruct M2S as (M1 & M2 & M3); split; [| split];
      [ apply (rw_cells_agree asegs m mm _ _ M1); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M2); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia
      | apply (rw_cells_agree asegs m mm _ _ M3); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy; cbn in Hy |- *; lia ])
  end.
  call (amemcpy_dst RIP usp d s n); [exact ST2| lia| unfold kHighShadowEnd; lia| lia| lia| lia| lia| lia| lia
        | exact CD2| exact M2S2| exact IC2| assumption|].
  lazymatch goal with H : stk asegs _ lo (usp + -2144) |- _ => rename H into ST3 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    assert (SRC : bytes_at asegs mm s src)
      by (unfold keep in SRC0; apply (bytes_at_agree asegs m mm _ _ SRC0); apply (agree_of_munch _ _ _ _ MUf); intros y Hy;
          cbn [outside]; fold n in Hy; (split; [lia| exact I]));
    assert (DST : rw_cells asegs mm d [CB (length src) junk])
      by (unfold keep in DST0; apply (rw_cells_agree asegs m mm _ _ DST0); [| exact WM]; apply (agree_of_munch _ _ _ _ MUf); intros y Hy;
          cbn [outside]; cbn [cells_size csize] in Hy; rewrite Nat.add_0_r in Hy; fold n in Hy; (split; [lia| exact I]))
  end.
  clear CD2 IC2 M2S2 MUf SRC0 DST0.
  (* [comment removed for export] *)
  assert (EUd : bv_unsigned (Z_to_bv 64 d) = d) by (apply unsigned_lit; lia).
  assert (EUs : bv_unsigned (Z_to_bv 64 s) = s) by (apply unsigned_lit; lia).
  assert (EUn : bv_unsigned (Z_to_bv 64 n) = n) by (apply unsigned_lit; lia).
  do 3 lstep.
  destruct (Z.eq_dec n 0) as [NZ0|NNZ].
  - (* [comment removed for export] *)
    eapply evt_cut.
    { eapply MC;
        [ rewrite EUs; exact SRC
        | rewrite EUn; unfold n; rewrite Nat2Z.id; reflexivity
        | rewrite EUd, EUn; unfold n; rewrite Nat2Z.id; exact DST
        | rewrite EUd, EUs, EUn; lia| rewrite EUd, EUn; lia| assumption]. }
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
    rewrite EUd, EUn in MUc. rewrite NZ0, Z.add_0_r in MUc.
    lazymatch type of MUc with munch _ ?m1 ?m2 =>
      assert (MUe : munch [] m1 m2) by (eapply munch_weaken; [| exact MUc]; unfold sub_fp; cbn [outside]; intros; lia);
      clear MUc; transport_after_call asegs m1 m2 MUe WMc; clear MUe WMc end.
    destruct_ands PO.
    replace (ret_pc (Z_to_bv 64 0x525cc)) with (Z_to_bv 64 0x525cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ?EUd, ?EUn, ?EUs in *.
    do 11 lstep.
    release_frame FR ST3 (usp + -72). release_frame FRs ST3 usp.
    lstep.
    unfold amemcpy_post. sys_finish.
    + rewrite (unsigned_lit usp) by lia.
      eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite (unsigned_lit usp) by lia. assumption.
    + lazymatch goal with H : rw_cells asegs _ d [CB _ src] |- _ => unfold n in H; rewrite Nat2Z.id in H; exact H end.
  - eapply evt_cut.
    { eapply MC;
        [ rewrite EUs; exact SRC
        | rewrite EUn; unfold n; rewrite Nat2Z.id; reflexivity
        | rewrite EUd, EUn; unfold n; rewrite Nat2Z.id; exact DST
        | rewrite EUd, EUs, EUn; lia| rewrite EUd, EUn; lia| assumption]. }
    intros ms' PO. destruct_exs PO. destruct PO as [E [MUc [WMc [MIc PO]]]]. subst ms'.
    rewrite EUd, EUn in MUc. rewrite EUd, EUn, EUs in PO.
    lazymatch type of MUc with munch _ ?m1 ?m2 =>
      assert (ST4 : stk asegs m2 lo (usp + -2144))
        by (destruct PO as [RWc _]; exact (stk_after_copy m1 m2 lo (usp + -2144) d n src ST3 MUc WMc RWc));
      clear ST3; rename ST4 into ST3;
      transport_after_call asegs m1 m2 MUc WMc; clear MUc WMc end.
    destruct_ands PO.
    replace (ret_pc (Z_to_bv 64 0x525cc)) with (Z_to_bv 64 0x525cc) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    rewrite ?EUd, ?EUn, ?EUs in *.
    do 11 lstep.
    release_frame FR ST3 (usp + -72). release_frame FRs ST3 usp.
    lstep.
    unfold amemcpy_post. sys_finish.
    + rewrite (unsigned_lit usp) by lia.
      eapply munch_weaken; [| exact MU]. unfold sub_fp; cbn [outside]; intros; lia.
    + rewrite (unsigned_lit usp) by lia. assumption.
    + lazymatch goal with H : rw_cells asegs _ d [CB _ src] |- _ => unfold n in H; rewrite Nat2Z.id in H; exact H end.
Qed.

End WithRIP.
