(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import RunCtx.  (* a worker (A1) tool *)
From LinuxProcessSemantics.LinuxProcessSem Require State Run.  (* a worker (A1) tool *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.World Require Import SrcO_zlib_zlib_uncompress3_fuzzer_repro.
Require Import OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.PropExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.CatSim OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SeqExec OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StepTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Hoare OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.WalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.StoreOk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.Frame OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.RefMemcpyLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.AgentLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.SumWalkTac OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzZ OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzCk OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzMem OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8AdlerBase OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8Adler_code OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8AdlerIface OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.FuzzAdlerLib OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8AdlerA OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.S8AdlerB.
From OSSVerify.Proofs.zlib.zlib_uncompress3_fuzzer.lib.ubsan_agrees_alloc_forced_only.cks Require Import CkTables CkModel CkMathAdler CkWalk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
#[local] Opaque adler32_z_model lo16 hi16 byte_at.

(* [comment removed for export] *)
Definition W8 (v : word) : list byte := word_to_le_bytes 8 v.
Definition M1 (m : word -> option byte) (usp : Z) (s0v s1v s2v : word) : word -> option byte :=
  wbytes (wbytes (wbytes m (Z_to_bv 64 (usp - 8)) (W8 s0v)) (Z_to_bv 64 (usp - 16)) (W8 s1v))
         (Z_to_bv 64 (usp - 24)) (W8 s2v).

Lemma lenW8' : forall v, length (W8 v) = 8%nat.
Proof. intros. apply lenW8. Qed.

Section FRAME.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variables (m : word -> option byte) (usp : Z) (s0v s1v s2v : word).
  Hypothesis Husp : 32 <= usp < two64.
  Hypothesis Hstk : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 32)) 32 = true.
  Hypothesis Himg : img_ok m.

  #[local] Abbreviation MM := (M1 m usp s0v s1v s2v).

  Lemma stk_slot : forall m' z, mem_grows m m' -> usp - 32 <= z -> z + 8 <= usp ->
    store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m' (Z_to_bv 64 z) 8 = true.
  Proof.
    intros m' z Hg Hlo Hhi. eapply store_ok_mono; [exact Hg|].
    eapply (store_ok_sub (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 32)) _ 32 8);
      [ rewrite u64_lit by lia; change (Z.of_nat 32) with 32; lia | exact Hstk
      | rewrite !u64_lit by lia; lia | rewrite !u64_lit by lia; change (Z.of_nat 8) with 8; change (Z.of_nat 32) with 32; lia ].
  Qed.

  Lemma grows_w : forall m0 (a : word) bs, mem_grows m m0 -> mem_grows m (wbytes m0 a bs).
  Proof. intros. eapply mem_grows_trans; [eassumption | apply wbytes_grows]. Qed.

  Lemma frame_off_ro32 : RO_HI <= usp - 32 \/ usp <= RO_LO.
  Proof.
    destruct (store_ok_off_ro m (usp - 32) 32 Hstk ltac:(lia) ltac:(change (Z.of_nat 32) with 32; lia)
                ltac:(change (Z.of_nat 32) with 32; lia) Himg); change (Z.of_nat 32) with 32 in *; lia.
  Qed.

  Lemma M1_img : img_ok MM.
  Proof.
    pose proof frame_off_ro32 as Hro. unfold M1.
    repeat (apply img_ok_wbytes; [| rewrite lenW8', u64_lit by lia; change (Z.of_nat 8) with 8; unfold RO_LO, RO_HI in *; lia
                                  | rewrite lenW8', u64_lit by lia; change (Z.of_nat 8) with 8; lia ]).
    exact Himg.
  Qed.

  Lemma M1_frame : frame_mod m MM [(Z_to_bv 64 (usp - 32), 32%Z)].
  Proof.
    unfold M1.
    assert (G : forall m0 z v, frame_mod m m0 [(Z_to_bv 64 (usp - 32), 32%Z)] -> usp - 32 <= z -> z + 8 <= usp ->
                 frame_mod m (wbytes m0 (Z_to_bv 64 z) (W8 v)) [(Z_to_bv 64 (usp - 32), 32%Z)]).
    { intros m0 z v Hf Hlo Hhi. eapply frame_mod_trans_same; [exact Hf|].
      eapply frame_mod_weaken; [| apply frame_mod_wbytes; rewrite lenW8', u64_lit by lia; change (Z.of_nat 8) with 8; lia].
      intros a [Ha _]. split; [|exact I]. rewrite lenW8'. change (Z.of_nat 8) with 8.
      intros Hin. apply Ha. unfold in_rng in *. rewrite !u64_lit in * by lia. lia. }
    apply G; [apply G; [apply G; [apply frame_mod_refl| lia | lia] | lia | lia] | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma M1_readable : forall adr len,
    (forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr + i)) 1 = Some [b]) ->
    (forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) MM (Z_to_bv 64 (adr + i)) 1 = Some [b]).
  Proof.
    intros adr len H i Hi. destruct (H i Hi) as [b Hb]. unfold M1.
    edestruct (rdn1_wbytes (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)) as [b1 Hb1]; [exact Hb|].
    edestruct (rdn1_wbytes (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)) as [b2 Hb2]; [exact Hb1|].
    edestruct (rdn1_wbytes (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb)) as [b3 Hb3]; [exact Hb2|].
    exists b3. exact Hb3.
  Qed.

  (* [comment removed for export] *)
  Lemma M1_rd_s0 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) MM (Z_to_bv 64 (usp - 8)) 8 = Some (W8 s0v).
  Proof.
    unfold M1. rewrite !rdn_wbytes_out_Z by (rewrite ?lenW8'; change (Z.of_nat 8) with 8; lia).
    apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia.
  Qed.
  Lemma M1_rd_s1 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) MM (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s1v).
  Proof.
    unfold M1. rewrite rdn_wbytes_out_Z by (rewrite ?lenW8'; change (Z.of_nat 8) with 8; lia).
    apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia.
  Qed.
  Lemma M1_rd_s2 : rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) MM (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s2v).
  Proof. unfold M1. apply rdn_wbytes_hit8. rewrite u64_lit by lia. lia. Qed.
End FRAME.

(* [comment removed for export] *)
Definition LPRO : list reg := [1; 3; 4; 5; 6; 7; 8; 9; 11; 12; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
Definition LEPI : list reg := [1; 3; 4; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.

Section RUN.
Context {RCa1 : RunCtx}.  (* a worker (A1) tool *)
  Variables (m rom : word -> option byte) (retw : word) (usp a adr len : Z).
  Hypothesis Hret : ret_ok retw.
  Hypothesis Ha : 0 <= a < two64.
  Hypothesis Hadr : 1 <= adr.
  Hypothesis Hlen : 0 <= len.
  Hypothesis Hnw : adr + len < two64.
  Hypothesis Husp : 32 <= usp < two64.
  Hypothesis Hstk : store_ok (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (usp - 32)) 32 = true.
  Hypothesis Hbelow : 1 <= len -> adr + len <= usp - 32.
  Hypothesis Himg : img_ok m.
  Hypothesis Hrd : forall i, 0 <= i < len -> exists b : byte, rdn (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) m (Z_to_bv 64 (adr + i)) 1 = Some [b].

  Ltac zbv := apply (f_equal (fun z : Z => Z_to_bv 64 z)); lia.
  Ltac solve_ka := first [ assumption | apply lkeeps_refl | solve_lkeeps ].
  Ltac post := repeat split; gres; rwR; first [ reflexivity | assumption | zbv | lia | solve_ka ].

  (* [comment removed for export] *)
  Ltac sd_z F D az oktac :=
    chain_step;
    [ reflexivity
    | eapply step_sd_at with (a := Z_to_bv 64 az);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi; zbv
      | gres; rwR; reflexivity
      | oktac ]
    | step_simpl ].

  (* [comment removed for export] *)
  Ltac ld_z F D vv az R :=
    chain_step;
    [ reflexivity
    | eapply step_ld with (v := vv);
      [ exact F | reflexivity | exact D
      | gres; imm_norm; rwR; rewrite ?zv_addi;
        match goal with |- rdn _ _ (Z_to_bv 64 ?x) _ = _ => replace x with az by lia end; exact R
      | apply bytes_le_to_Z_8 ]
    | step_simpl; gres ].

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  (* [comment removed for export] *)
End RUN.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Theorem s8_adler32_z_null {RCa1 : RunCtx}  : S8_adler32_z_null_stmt.
Proof.
  intros regs m rom retw R1 Hret R11 R12.
  eexists. split; [|split].
  - stepz F_17194 D_17194.
    stepz F_17198 D_17198.
    stepz F_1719c D_1719c.
    stepi F_171a0 D_171a0; znorm.
    stepb_tk F_171a4 D_171a4 ltac:(condZ).
    stepb_tk F_171f8 D_171f8 ltac:(condZ).
    stepret F_171f4 D_171f4 retw ltac:(rwR; reflexivity).
    apply mst_refl.
  - gres. reflexivity.
  - apply (proj2 (keeps_cs_lkeeps _ _)). solve_lkeeps.
Qed.

(* [comment removed for export] *)
Lemma wrap_run {RCa1 : RunCtx}  : forall regs m rom (v : Z),
  getr regs 12 = Z_to_bv 64 v -> 0 <= v < two64 ->
  exists r, msteps (LinuxProcessSemantics.LinuxProcessSem.Run.run_segments RSEGS rc_inp rc_sp rc_mb) (mkst regs (0x176a4 : word) m rom) (mkst r (0x172e0 : word) m rom)
    /\ getr r 12 = Z_to_bv 64 (v mod 2 ^ 32)
    /\ r = regupd (regupd regs 12 (Z_to_bv 64 (v * 2 ^ 32))) 12 (Z_to_bv 64 (v mod two32)).
Proof.
  intros regs m rom v R12 Hv.
  eexists. split; [|split].
  - stepz F_17558 D_17558. stepz F_1755c D_1755c. stepz F_17560 D_17560. apply mst_refl.
  - gres. change (2 ^ 32) with two32. reflexivity.
  - reflexivity.
Qed.

(* [comment removed for export] *)

Theorem s8_adler32_null {RCa1 : RunCtx}  : S8_adler32_null_stmt.
Proof.
  intros regs m rom retw R1 Hret R11 R12.
  destruct (wrap_run regs m rom 0 R12 ltac:(lia)) as (r0 & M0 & S12 & Er0).
  assert (G : forall x : reg, x <> 12%bv -> getr r0 x = getr regs x).
  { intros x Hx. subst r0. rewrite !getr_other by (exact Hx). reflexivity. }
  destruct (s8_adler32_z_null r0 m rom retw ltac:(rewrite G by (intros E; discriminate E); exact R1) Hret
              ltac:(rewrite G by (intros E; discriminate E); exact R11) S12) as (r & M & V & K).
  exists r. split; [|split; [exact V|]].
  - eapply msteps_trans; [exact M0 | exact M].
  - intros x Hx. rewrite (K x Hx). apply G. intros ->. cbv in Hx. intuition discriminate.
Qed.
