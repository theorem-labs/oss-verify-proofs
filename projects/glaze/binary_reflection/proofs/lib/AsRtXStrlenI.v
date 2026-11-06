(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtM2SI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_m2s_tab_55aa8 : m2s_tab :=
  {| mt_base := 0x55ab0; mt_g_shoff := 0xff270; mt_p_shoff := 0x107578; mt_g_midbeg := 0xff278; mt_p_midbeg := 0x108268;
     mt_g_midend := 0xff280; mt_p_midend := 0x108270; mt_g_hiend := 0xff288; mt_p_hiend := 0x108260 |}.
Definition asan_m2s_tab_577b0 : m2s_tab :=
  {| mt_base := 0x577b8; mt_g_shoff := 0xff270; mt_p_shoff := 0x107578; mt_g_midbeg := 0xff278; mt_p_midbeg := 0x108268;
     mt_g_midend := 0xff280; mt_p_midend := 0x108270; mt_g_hiend := 0xff288; mt_p_hiend := 0x108260 |}.
Definition asan_m2s_tab_6e03c : m2s_tab :=
  {| mt_base := 0x6e044; mt_g_shoff := 0xff270; mt_p_shoff := 0x107578; mt_g_midbeg := 0xff278; mt_p_midbeg := 0x108268;
     mt_g_midend := 0xff280; mt_p_midend := 0x108270; mt_g_hiend := 0xff288; mt_p_hiend := 0x108260 |}.
Definition asan_m2s_tab_6fb04 : m2s_tab :=
  {| mt_base := 0x6fb0c; mt_g_shoff := 0xff270; mt_p_shoff := 0x107578; mt_g_midbeg := 0xff278; mt_p_midbeg := 0x108268;
     mt_g_midend := 0xff280; mt_p_midend := 0x108270; mt_g_hiend := 0xff288; mt_p_hiend := 0x108260 |}.
Definition asan_m2s_tab_79180 : m2s_tab :=
  {| mt_base := 0x79188; mt_g_shoff := 0xff270; mt_p_shoff := 0x107578; mt_g_midbeg := 0xff278; mt_p_midbeg := 0x108268;
     mt_g_midend := 0xff280; mt_p_midend := 0x108270; mt_g_hiend := 0xff288; mt_p_hiend := 0x108260 |}.

Ltac tabred := (lazymatch goal with |- ?G => let G' := eval cbn [mt_base mt_g_shoff mt_p_shoff mt_g_midbeg mt_p_midbeg mt_g_midend mt_p_midend mt_g_hiend mt_p_hiend
                    asan_m2s_tab_55aa8 asan_m2s_tab_577b0 asan_m2s_tab_6e03c asan_m2s_tab_6fb04 asan_m2s_tab_79180] in G in change_no_check G' end).

Section FPGen1.
Context {fx : FPState}.


Lemma asan_m2s_tab_ok_577b0 : m2s_tab_ok ASEGS asan_m2s_tab_577b0.
Proof using.
  split; tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold m2s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_577b0 D_577b0 F_577b4 D_577b4.
  - gload_tac F_577d0 D_577d0 F_577d4 D_577d4.
  - gload_tac F_577d8 D_577d8 F_577dc D_577dc.
  - gload_tac F_577f4 D_577f4 F_577f8 D_577f8.
Qed.

Lemma asan_m2s_tab_ok_6e03c : m2s_tab_ok ASEGS asan_m2s_tab_6e03c.
Proof using.
  split; tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold m2s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6e03c D_6e03c F_6e040 D_6e040.
  - gload_tac F_6e05c D_6e05c F_6e060 D_6e060.
  - gload_tac F_6e064 D_6e064 F_6e068 D_6e068.
  - gload_tac F_6e080 D_6e080 F_6e084 D_6e084.
Qed.

Lemma asan_m2s_tab_ok_6fb04 : m2s_tab_ok ASEGS asan_m2s_tab_6fb04.
Proof using.
  split; tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold m2s_words in G in change_no_check G' end). code_ato_vm.
  - gload_tac F_6fb04 D_6fb04 F_6fb08 D_6fb08.
  - gload_tac F_6fb24 D_6fb24 F_6fb28 D_6fb28.
  - gload_tac F_6fb2c D_6fb2c F_6fb30 D_6fb30.
  - gload_tac F_6fb48 D_6fb48 F_6fb4c D_6fb4c.
Qed.








End FPGen1.
End AsRtM2SI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtRegionI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Abbreviation ASEGS := Asan.M.loaded_segments.

Ltac tabred := (lazymatch goal with |- ?G => let G' := eval cbn [mt_base mt_g_shoff mt_p_shoff mt_g_midbeg mt_p_midbeg mt_g_midend mt_p_midend mt_g_hiend mt_p_hiend
                    rt_base rt_m2s asan_m2s_tab_6fb04] in G in change_no_check G' end).

Section FPGen1.
Context {fx : FPState}.

Definition asan_rip_tab : rip_tab := {| rt_base := 0x6ff98; rt_m2s := asan_m2s_tab_6fb04 |}.

Lemma asan_rip_tab_ok : rip_tab_ok ASEGS asan_rip_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [rt_base rt_m2s asan_rip_tab] in G in change_no_check G' end); tabred.
  - (lazymatch goal with |- ?G => let G' := eval unfold rip_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_m2s_tab_ok_6fb04.
  - apply bv_eq. vm_compute. reflexivity.
  - replace (at_ (0x6ff98 : word) 66768) with (0x80468 : word) by (apply bv_eq; vm_compute; reflexivity).
    exact asan_mem_is_zero_code.
  - gload_tac F_6ffbc D_6ffbc F_6ffc0 D_6ffc0.
  - gload_tac F_6ffdc D_6ffdc F_6ffe0 D_6ffe0.
  - gload_tac F_6ffe4 D_6ffe4 F_6ffe8 D_6ffe8.
  - gload_tac F_70000 D_70000 F_70004 D_70004.
  - gload_tac F_70024 D_70024 F_70028 D_70028.
  - gload_tac F_7002c D_7002c F_70030 D_70030.
  - gload_tac F_70048 D_70048 F_7004c D_7004c.
  - imm_norm. lia.
Qed.

(* [comment removed for export] *)
Theorem asan_region_clear : forall mem rom (beg size ra sp : word) (s0b s1b : byte) (midend : word) regs,
  ripH ASEGS asan_rip_tab mem beg size ra sp s0b s1b midend ->
  getr regs 1 = ra -> getr regs 2 = sp -> getr regs 10 = beg -> getr regs 11 = size ->
  exists r,
    msteps ASEGS (mkst regs (0x6ff98 : word) mem rom)
                 (mkst r ra (rip_mem asan_rip_tab mem sp ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19)
                                     (getr regs 20) (getr regs 21) beg size) rom)
    /\ getr r 10 = Z_to_bv 64 0
    /\ regs_agree (fun r => In r rip_clob) regs r.
Proof using. exact (region_clear ASEGS asan_rip_tab asan_rip_tab_ok). Qed.
End FPGen1.
End AsRtRegionI.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4 OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsDrvQcSlow.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Spec4.AgentLib OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.
#[local] Abbreviation LE8 z := (word_to_le_bytes 8 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Definition QSB : Z := 0x7fff8000.
Definition QKHIMEM : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition shok_sem (M : word -> option byte) (A N : Z) : Prop :=
  forall z, (A <= z < A + N)%Z -> exists b : byte, M (Z_to_bv 64 (QSB + z / 8)) = Some b /\ (U b = 0 \/ z mod 8 < U b <= 7)%Z.

Lemma div8_mul8_le : forall x, (0 <= x -> x / 8 * 8 <= x /\ x < x / 8 * 8 + 8)%Z.
Proof. intros x Hx. pose proof (Z.div_mod x 8 ltac:(lia)). pose proof (Z.mod_pos_bound x 8 ltac:(lia)). lia. Qed.

(* [comment removed for export] *)
Lemma shok_granule0 : forall M A N g,
  shok_sem M A N -> (A <= 8 * g)%Z -> (8 * g + 8 <= A + N)%Z -> M (Z_to_bv 64 (QSB + g)) = Some (Z_to_bv 8 0).
Proof.
  intros M A N g HS H1 H2.
  destruct (HS (8 * g + 7)%Z ltac:(lia)) as (b & Hb & Hv).
  replace ((8 * g + 7) / 8)%Z with g in Hb by (apply Z.div_unique with (r := 7%Z); lia).
  rewrite Hb. f_equal. apply bv_eq.
  pose proof (bv_unsigned_in_range _ b) as Rb. change (bv_modulus 8) with 256%Z in Rb.
  replace ((8 * g + 7) mod 8)%Z with 7%Z in Hv by (apply Z.mod_unique with (q := g); lia).
  assert (Hu : U b = 0%Z) by lia.
  rewrite Z_to_bv_unsigned. change (bv_wrap 8 0) with 0%Z. exact Hu.
Qed.

Lemma rdn1_of_mem : forall (mem : word -> option byte) (a : word) (b : byte), mem a = Some b -> rdn ASEGS mem a 1 = Some [b].
Proof. intros mem a b H. cbn [rdn]. rewrite H. reflexivity. Qed.

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma ripH_of_shok_gen : forall (mem : word -> option byte) (b ra : word) (A N n spz me : Z),
  (8 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n <= A + N)%Z -> shok_sem mem A N ->
  ((QKHIMEM <= U b /\ U b + n + 1 <= 2 ^ 47) \/ U b + n <= 0x7fff7fff)%Z ->
  rdn ASEGS mem (Z_to_bv 64 0xff270) 8 = Some (LE8 0x107578) -> rdn ASEGS mem (Z_to_bv 64 0xff278) 8 = Some (LE8 0x108268) ->
  rdn ASEGS mem (Z_to_bv 64 0xff280) 8 = Some (LE8 0x108270) -> rdn ASEGS mem (Z_to_bv 64 0xff288) 8 = Some (LE8 0x108260) ->
  rdn ASEGS mem (Z_to_bv 64 0x107578) 8 = Some (LE8 0x7fff8000) -> rdn ASEGS mem (Z_to_bv 64 0x108268) 8 = Some (LE8 0) ->
  rdn ASEGS mem (Z_to_bv 64 0x108260) 8 = Some (LE8 0x7fffffffffff) ->
  rdn ASEGS mem (Z_to_bv 64 0x108270) 8 = Some (LE8 me) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok ASEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  ret_ok ra ->
  exists s0b s1b : byte, ripH ASEGS asan_rip_tab mem b (Z_to_bv 64 n) ra (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me).
Proof.
  intros mem b ra A N n spz me Hn HA HN HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk Hra.
  pose proof (u64_range b) as Rb.
  assert (Un : U (Z_to_bv 64 n) = n) by (apply u64_lit; lia).
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in *; lia).
  destruct (HS (U b) ltac:(lia)) as (s0b & Hs0 & Hs0v).
  destruct (HS (U b + n - 1)%Z ltac:(lia)) as (s1b & Hs1 & Hs1v).
  exists s0b, s1b. split; cbn [rt_m2s rt_base asan_rip_tab]; rewrite ?Un, ?Usp.
  - split; tabred; try assumption.
    + unfold m2s_cells. tabred. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
    + unfold QKHIMEM in Hrng. lia.
    + unfold QKHIMEM in Hrng. lia.
  - unfold m2s_cells. tabred. unfold QKHIMEM in Hsp1. repeat (apply Forall_cons; [lia|]). apply Forall_nil.
  - lia.
  - unfold QKHIMEM in Hrng. lia.
  - lia.
  - apply rdn1_of_mem. unfold Sh. rewrite <- Hs0. f_equal. f_equal. unfold QSB. lia.
  - lia.
  - apply rdn1_of_mem. unfold Sh. rewrite <- Hs1. f_equal. f_equal. unfold QSB. lia.
  - lia.
  - intros a Ha. unfold Sh, up8, down8 in Ha.
    replace a with (Z_to_bv 64 (QSB + (U a - QSB))) by (rewrite <- (Z_to_bv_bv_unsigned _ a) at 2; f_equal; lia).
    apply rdn1_of_mem. apply (shok_granule0 mem A N (U a - QSB) HS).
    + pose proof (div8_mul8_le (U b + 7) ltac:(lia)) as [D1 D2]. unfold QSB in *.
      assert ((U b + 7) / 8 * 8 / 8 = (U b + 7) / 8)%Z by (apply Z.div_mul; lia). lia.
    + pose proof (div8_mul8_le (U b + n) ltac:(lia)) as [D1 D2]. unfold QSB in *.
      assert ((U b + n) / 8 * 8 / 8 = (U b + n) / 8)%Z by (apply Z.div_mul; lia). lia.
  - unfold QKHIMEM in Hsp1. lia.
  - replace (at_ (Z_to_bv 64 spz) (-80)) with (Z_to_bv 64 (spz - 80)); [exact Hstk|].
    apply bv_eq. rewrite at_u by (rewrite Usp; unfold QKHIMEM in Hsp1; lia). rewrite Usp. apply u64_lit. unfold QKHIMEM in Hsp1. lia.
  - exact Hra.
Qed.
Lemma ripH_of_shok : forall (mem : word -> option byte) (b ra : word) (A N n spz me : Z),
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn ASEGS mem (Z_to_bv 64 0xff270) 8 = Some (LE8 0x107578) -> rdn ASEGS mem (Z_to_bv 64 0xff278) 8 = Some (LE8 0x108268) ->
  rdn ASEGS mem (Z_to_bv 64 0xff280) 8 = Some (LE8 0x108270) -> rdn ASEGS mem (Z_to_bv 64 0xff288) 8 = Some (LE8 0x108260) ->
  rdn ASEGS mem (Z_to_bv 64 0x107578) 8 = Some (LE8 0x7fff8000) -> rdn ASEGS mem (Z_to_bv 64 0x108268) 8 = Some (LE8 0) ->
  rdn ASEGS mem (Z_to_bv 64 0x108260) 8 = Some (LE8 0x7fffffffffff) ->
  rdn ASEGS mem (Z_to_bv 64 0x108270) 8 = Some (LE8 me) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok ASEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  ret_ok ra ->
  exists s0b s1b : byte, ripH ASEGS asan_rip_tab mem b (Z_to_bv 64 n) ra (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me).
Proof.
  intros mem b ra A N n spz me Hn HA0 HAN H47 HS Hrng.
  apply (ripH_of_shok_gen mem b ra A N n spz me); try assumption; try lia.
Qed.

(* [comment removed for export] *)
Lemma rip_mem_post : forall (mem : word -> option byte) (sp ra s0 s1 s2 s3 s4 s5 beg size : word),
  (80 <= U sp)%Z ->
  (forall x : word, (U x < U sp - 80 \/ U sp <= U x)%Z -> rip_mem asan_rip_tab mem sp ra s0 s1 s2 s3 s4 s5 beg size x = mem x)
  /\ mem_grows mem (rip_mem asan_rip_tab mem sp ra s0 s1 s2 s3 s4 s5 beg size).
Proof.
  intros mem sp ra s0 s1 s2 s3 s4 s5 beg size Hsp. split.
  - intros x Hx. apply rip_mem_outside; assumption.
  - unfold rip_mem, ps_frame. destruct (Z.ltb _ _); repeat (eapply mem_grows_trans; [|apply wbytes_grows]); apply mem_grows_refl.
Qed.

(* [comment removed for export] *)
Lemma qc_slow_strnlen : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (A N n spz : Z),
  getr regs 18 = b -> getr regs 9 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn ASEGS mem (Z_to_bv 64 0xff270) 8 = Some (LE8 0x107578) -> rdn ASEGS mem (Z_to_bv 64 0xff278) 8 = Some (LE8 0x108268) ->
  rdn ASEGS mem (Z_to_bv 64 0xff280) 8 = Some (LE8 0x108270) -> rdn ASEGS mem (Z_to_bv 64 0xff288) 8 = Some (LE8 0x108260) ->
  rdn ASEGS mem (Z_to_bv 64 0x107578) 8 = Some (LE8 0x7fff8000) -> rdn ASEGS mem (Z_to_bv 64 0x108268) 8 = Some (LE8 0) ->
  rdn ASEGS mem (Z_to_bv 64 0x108260) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn ASEGS mem (Z_to_bv 64 0x108270) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok ASEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps ASEGS (mkst regs (0x5c88c : word) mem rom) (mkst r (0x5c8d4 : word) mem' rom)
    /\ regs_agree (fun x => In x [1; 5; 11; 12; 13; 14; 15; 16; 17; 18; 22]%list) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b A N n spz Rb Rn Rsp Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  assert (RA : ret_ok (Z_to_bv 64 0x5c9d0)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (ripH_of_shok mem b (Z_to_bv 64 0x5c9d0) A N n spz me Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  set (r1 := regupd (regupd (regupd (regupd (regupd regs 11 (Z_to_bv 64 (n - 65))) 12 (Z_to_bv 64 (2 ^ 64 - 65))) 22 (getr regs 10)) 10 b) 11 (Z_to_bv 64 n)).
  set (r1' := regupd r1 1 (Z_to_bv 64 0x5c9d0)).
  destruct (asan_region_clear mem rom b (Z_to_bv 64 n) (Z_to_bv 64 0x5c9d0) (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) r1' PH)
    as (r2 & RUN2 & A10 & AG2); [subst r1' r1; gres; reflexivity | subst r1' r1; gres; exact Rsp | subst r1' r1; gres; reflexivity | subst r1' r1; gres; reflexivity |].
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) (Z_to_bv 64 0x5c9d0) (getr r1' 8) (getr r1' 9) (getr r1' 18) (getr r1' 19) (getr r1' 20) (getr r1' 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  eexists. eexists. split; [|split; [|split; [exact MO | exact MG]]].
  - av F_5c884 D_5c884 (Z_to_bv 64 (n - 65)) ltac:(unfold v_addi; unorm; f_equal; lia).      (* [comment removed for export] *)
    av F_5c888 D_5c888 (Z_to_bv 64 (2 ^ 64 - 65)) ltac:(apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    ab_tk F_5c88c D_5c88c ltac:(condz).               (* [comment removed for export] *)
    ab_tk F_5c97c D_5c97c ltac:(condz).               (* [comment removed for export] *)
    an F_5c9b8 D_5c9b8.                               (* [comment removed for export] *)
    an F_5c9bc D_5c9bc.                               (* [comment removed for export] *)
    an F_5c9c0 D_5c9c0.                               (* [comment removed for export] *)
    an F_5c9c4 D_5c9c4.                               (* [comment removed for export] *)
    change (regupd _ 1 _) with r1'.
    eapply msteps_trans; [exact RUN2|]. lit_pc.
    an F_5c9c8 D_5c9c8.                               (* [comment removed for export] *)
    an F_5c9cc D_5c9cc.                               (* [comment removed for export] *)
    ab_tk F_5c9d0 D_5c9d0 ltac:(condz).               (* [comment removed for export] *)
    apply mst_refl.
  - intros x Hx.
    assert (X : x <> 1 /\ x <> 5 /\ x <> 11 /\ x <> 12 /\ x <> 13 /\ x <> 14 /\ x <> 15 /\ x <> 16 /\ x <> 17 /\ x <> 18 /\ x <> 22)
      by (repeat split; intros ->; apply Hx; cbn; tauto).
    destruct X as (X1 & X5 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X22).
    destruct (bv_eq_dec _ x 10) as [->|N10].
    + gres. rewrite (AG2 22) by notin. subst r1' r1. gres. reflexivity.
    + rewrite !getr_other by assumption.
      rewrite (AG2 x) by (unfold rip_clob; cbn [In]; intros Hc; repeat (destruct Hc as [<-|Hc]; [congruence|]); exact Hc).
      subst r1' r1. rewrite !getr_other by assumption. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma qc_slow_memchr : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (A N n spz : Z),
  getr regs 18 = b -> getr regs 9 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn ASEGS mem (Z_to_bv 64 0xff270) 8 = Some (LE8 0x107578) -> rdn ASEGS mem (Z_to_bv 64 0xff278) 8 = Some (LE8 0x108268) ->
  rdn ASEGS mem (Z_to_bv 64 0xff280) 8 = Some (LE8 0x108270) -> rdn ASEGS mem (Z_to_bv 64 0xff288) 8 = Some (LE8 0x108260) ->
  rdn ASEGS mem (Z_to_bv 64 0x107578) 8 = Some (LE8 0x7fff8000) -> rdn ASEGS mem (Z_to_bv 64 0x108268) 8 = Some (LE8 0) ->
  rdn ASEGS mem (Z_to_bv 64 0x108260) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn ASEGS mem (Z_to_bv 64 0x108270) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok ASEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps ASEGS (mkst regs (0x5dd3c : word) mem rom) (mkst r (0x5dd84 : word) mem' rom)
    /\ regs_agree (fun x => In x [1; 5; 11; 12; 13; 14; 15; 16; 17; 18; 21]%list) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b A N n spz Rb Rn Rsp Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  assert (RA : ret_ok (Z_to_bv 64 0x5debc)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (ripH_of_shok mem b (Z_to_bv 64 0x5debc) A N n spz me Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  set (r1 := regupd (regupd (regupd (regupd (regupd regs 11 (Z_to_bv 64 (n - 65))) 12 (Z_to_bv 64 (2 ^ 64 - 65))) 21 (getr regs 10)) 10 b) 11 (Z_to_bv 64 n)).
  set (r1' := regupd r1 1 (Z_to_bv 64 0x5debc)).
  destruct (asan_region_clear mem rom b (Z_to_bv 64 n) (Z_to_bv 64 0x5debc) (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) r1' PH)
    as (r2 & RUN2 & A10 & AG2); [subst r1' r1; gres; reflexivity | subst r1' r1; gres; exact Rsp | subst r1' r1; gres; reflexivity | subst r1' r1; gres; reflexivity |].
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) (Z_to_bv 64 0x5debc) (getr r1' 8) (getr r1' 9) (getr r1' 18) (getr r1' 19) (getr r1' 20) (getr r1' 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  eexists. eexists. split; [|split; [|split; [exact MO | exact MG]]].
  - av F_5dd34 D_5dd34 (Z_to_bv 64 (n - 65)) ltac:(unfold v_addi; unorm; f_equal; lia).      (* [comment removed for export] *)
    av F_5dd38 D_5dd38 (Z_to_bv 64 (2 ^ 64 - 65)) ltac:(apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    ab_tk F_5dd3c D_5dd3c ltac:(condz).               (* [comment removed for export] *)
    ab_tk F_5de68 D_5de68 ltac:(condz).               (* [comment removed for export] *)
    an F_5dea4 D_5dea4.                               (* [comment removed for export] *)
    an F_5dea8 D_5dea8.                               (* [comment removed for export] *)
    an F_5deac D_5deac.                               (* [comment removed for export] *)
    an F_5deb0 D_5deb0.                               (* [comment removed for export] *)
    change (regupd _ 1 _) with r1'.
    eapply msteps_trans; [exact RUN2|]. lit_pc.
    an F_5deb4 D_5deb4.                               (* [comment removed for export] *)
    an F_5deb8 D_5deb8.                               (* [comment removed for export] *)
    ab_tk F_5debc D_5debc ltac:(condz).               (* [comment removed for export] *)
    apply mst_refl.
  - intros x Hx.
    assert (X : x <> 1 /\ x <> 5 /\ x <> 11 /\ x <> 12 /\ x <> 13 /\ x <> 14 /\ x <> 15 /\ x <> 16 /\ x <> 17 /\ x <> 18 /\ x <> 21)
      by (repeat split; intros ->; apply Hx; cbn; tauto).
    destruct X as (X1 & X5 & X11 & X12 & X13 & X14 & X15 & X16 & X17 & X18 & X21).
    destruct (bv_eq_dec _ x 10) as [->|N10].
    + gres. rewrite (AG2 21) by notin. subst r1' r1. gres. reflexivity.
    + rewrite !getr_other by assumption.
      rewrite (AG2 x) by (unfold rip_clob; cbn [In]; intros Hc; repeat (destruct Hc as [<-|Hc]; [congruence|]); exact Hc).
      subst r1' r1. rewrite !getr_other by assumption. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma qc_slow_printf : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b : word) (A N n spz : Z),
  getr regs 22 = b -> getr regs 23 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (65 <= n <= 2 ^ 43)%Z -> (0 <= A <= U b)%Z -> (U b + n + 1 <= A + N)%Z -> (A + N <= 2 ^ 47)%Z -> shok_sem mem A N ->
  (QKHIMEM <= U b \/ U b + n <= 0x7fff7fff)%Z ->
  rdn ASEGS mem (Z_to_bv 64 0xff270) 8 = Some (LE8 0x107578) -> rdn ASEGS mem (Z_to_bv 64 0xff278) 8 = Some (LE8 0x108268) ->
  rdn ASEGS mem (Z_to_bv 64 0xff280) 8 = Some (LE8 0x108270) -> rdn ASEGS mem (Z_to_bv 64 0xff288) 8 = Some (LE8 0x108260) ->
  rdn ASEGS mem (Z_to_bv 64 0x107578) 8 = Some (LE8 0x7fff8000) -> rdn ASEGS mem (Z_to_bv 64 0x108268) 8 = Some (LE8 0) ->
  rdn ASEGS mem (Z_to_bv 64 0x108260) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn ASEGS mem (Z_to_bv 64 0x108270) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok ASEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps ASEGS (mkst regs (0x5f3ac : word) mem rom) (mkst r (0x5f300 : word) mem' rom)
    /\ regs_agree (fun x => In x [1; 5; 10; 11; 12; 13; 14; 15; 16; 17]%list) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b A N n spz Rb Rn Rsp Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  assert (RA : ret_ok (Z_to_bv 64 0x5f434)) by (apply bv_eq; vm_compute; reflexivity).
  destruct (ripH_of_shok mem b (Z_to_bv 64 0x5f434) A N n spz me Hn HA0 HAN H47 HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  set (r1 := regupd (regupd (regupd (regupd regs 10 (Z_to_bv 64 (n - 65))) 11 (Z_to_bv 64 (2 ^ 64 - 65))) 10 b) 11 (Z_to_bv 64 n)).
  set (r1' := regupd r1 1 (Z_to_bv 64 0x5f434)).
  destruct (asan_region_clear mem rom b (Z_to_bv 64 n) (Z_to_bv 64 0x5f434) (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) r1' PH)
    as (r2 & RUN2 & A10 & AG2); [subst r1' r1; gres; reflexivity | subst r1' r1; gres; exact Rsp | subst r1' r1; gres; reflexivity | subst r1' r1; gres; reflexivity |].
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) (Z_to_bv 64 0x5f434) (getr r1' 8) (getr r1' 9) (getr r1' 18) (getr r1' 19) (getr r1' 20) (getr r1' 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  eexists. eexists. split; [|split; [|split; [exact MO | exact MG]]].
  - av F_5f3a4 D_5f3a4 (Z_to_bv 64 (n - 65)) ltac:(unfold v_addi; unorm; f_equal; lia).      (* [comment removed for export] *)
    av F_5f3a8 D_5f3a8 (Z_to_bv 64 (2 ^ 64 - 65)) ltac:(apply bv_eq; vm_compute; reflexivity).  (* [comment removed for export] *)
    ab_tk F_5f3ac D_5f3ac ltac:(condz).               (* [comment removed for export] *)
    ab_tk F_5f66c D_5f66c ltac:(condz).               (* [comment removed for export] *)
    an F_5f420 D_5f420.                               (* [comment removed for export] *)
    an F_5f424 D_5f424.                               (* [comment removed for export] *)
    an F_5f428 D_5f428.                               (* [comment removed for export] *)
    change (regupd _ 1 _) with r1'.
    eapply msteps_trans; [exact RUN2|]. lit_pc.
    ab_tk F_5f42c D_5f42c ltac:(condz).               (* [comment removed for export] *)
    apply mst_refl.
  - intros x Hx.
    assert (X : x <> 1 /\ x <> 5 /\ x <> 10 /\ x <> 11 /\ x <> 12 /\ x <> 13 /\ x <> 14 /\ x <> 15 /\ x <> 16 /\ x <> 17)
      by (repeat split; intros ->; apply Hx; cbn; tauto).
    destruct X as (X1 & X5 & X10 & X11 & X12 & X13 & X14 & X15 & X16 & X17).
    rewrite (AG2 x) by (unfold rip_clob; cbn [In]; intros Hc; repeat (destruct Hc as [<-|Hc]; [congruence|]); exact Hc).
    subst r1' r1. rewrite !getr_other by assumption. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma region_call_clear : forall (regs : bvmap 5 word) (mem rom : word -> option byte) (b ra : word) (n spz : Z),
  getr regs 1 = ra -> ret_ok ra -> getr regs 10 = b -> getr regs 11 = Z_to_bv 64 n -> getr regs 2 = Z_to_bv 64 spz ->
  (8 <= n <= 2 ^ 43)%Z -> shok_sem mem (U b) n ->
  ((QKHIMEM <= U b /\ U b + n + 1 <= 2 ^ 47) \/ U b + n <= 0x7fff7fff)%Z ->
  rdn ASEGS mem (Z_to_bv 64 0xff270) 8 = Some (LE8 0x107578) -> rdn ASEGS mem (Z_to_bv 64 0xff278) 8 = Some (LE8 0x108268) ->
  rdn ASEGS mem (Z_to_bv 64 0xff280) 8 = Some (LE8 0x108270) -> rdn ASEGS mem (Z_to_bv 64 0xff288) 8 = Some (LE8 0x108260) ->
  rdn ASEGS mem (Z_to_bv 64 0x107578) 8 = Some (LE8 0x7fff8000) -> rdn ASEGS mem (Z_to_bv 64 0x108268) 8 = Some (LE8 0) ->
  rdn ASEGS mem (Z_to_bv 64 0x108260) 8 = Some (LE8 0x7fffffffffff) ->
  (exists me : Z, rdn ASEGS mem (Z_to_bv 64 0x108270) 8 = Some (LE8 me)) ->
  (QKHIMEM + 80 <= spz)%Z -> (spz + 16 <= 2 ^ 47)%Z -> store_ok ASEGS mem (Z_to_bv 64 (spz - 80)) 80 = true ->
  exists r mem', msteps ASEGS (mkst regs (0x6ff98 : word) mem rom) (mkst r ra mem' rom)
    /\ getr r 10 = Z_to_bv 64 0 /\ regs_agree (fun x => In x rip_clob) regs r
    /\ (forall x : word, (U x < spz - 80 \/ spz <= U x)%Z -> mem' x = mem x) /\ mem_grows mem mem'.
Proof.
  intros regs mem rom b ra n spz R1 RA R10 R11 Rsp Hn HS Hrng C1 C2 C3 C4 C5 C6 C7 [me C8] Hsp1 Hsp2 Hstk.
  pose proof (u64_range b) as Rb.
  destruct (ripH_of_shok_gen mem b ra (U b) n n spz me Hn ltac:(lia) ltac:(lia) HS Hrng C1 C2 C3 C4 C5 C6 C7 C8 Hsp1 Hsp2 Hstk RA) as (s0b & s1b & PH).
  destruct (asan_region_clear mem rom b (Z_to_bv 64 n) ra (Z_to_bv 64 spz) s0b s1b (Z_to_bv 64 me) regs PH R1 Rsp R10 R11) as (r2 & RUN2 & A10 & AG2).
  assert (Usp : U (Z_to_bv 64 spz) = spz) by (apply u64_lit; unfold QKHIMEM in Hsp1; lia).
  destruct (rip_mem_post mem (Z_to_bv 64 spz) ra (getr regs 8) (getr regs 9) (getr regs 18) (getr regs 19) (getr regs 20) (getr regs 21) b (Z_to_bv 64 n)
              ltac:(rewrite Usp; unfold QKHIMEM in Hsp1; lia)) as [MO MG].
  rewrite Usp in MO.
  exists r2. eexists. split; [exact RUN2|]. split; [exact A10|]. split; [exact AG2|]. split; [exact MO | exact MG].
Qed.

End FPGen.
End AsDrvQcSlow.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsRtStrlenI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_strlen_tab : strlen_tab := {| st_base := 0xf5930; st_cM := 0x10408; st_cH := 0x103e8 |}.

Section FPGen1.
Context {fx : FPState}.

Lemma asan_sl_consts : sl_consts ASEGS (0xf5930 : word) 0x10408 0x103e8.
Proof using.
  (lazymatch goal with |- ?G => let G' := eval unfold sl_consts in G in change_no_check G' end). wd_eexists. wd_eexists. intros regs mem rom vM vH RM RH.
  replace (at_ (0xf5930 : word) 60) with (0xf596c : word) by (apply bv_eq; vm_compute; reflexivity).
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_f5970 | reflexivity | exact D_f5970] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_f5974 | reflexivity | exact D_f5974] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step;
   [ reflexivity
   | eapply step_ld with (bs := word_to_le_bytes 8 vM) (v := vM);
     [exact F_f5978 | reflexivity | exact D_f5978 | | apply bytes_le_to_Z_8];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact RM
   | step_simpl ]).
  (chain_step;
   [ reflexivity
   | eapply step_ld with (bs := word_to_le_bytes 8 vH) (v := vH);
     [exact F_f597c | reflexivity | exact D_f597c | | apply bytes_le_to_Z_8];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact RH
   | step_simpl ]).
  close_refl.
Qed.

Lemma asan_strlen_tab_ok : strlen_tab_ok ASEGS asan_strlen_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [st_base st_cM st_cH asan_strlen_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold mstrlen_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_sl_consts.
Qed.

End FPGen1.
End AsRtStrlenI.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import WalkLetEv.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.Frame OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsCodeM5 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemIsZero OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtM2S AsRtM2SI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion AsRtRegionI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset.AsRtQC OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtAMemset OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtMemchr OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtStrlen AsRtStrlenI OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtTlsGA.AsRtXStrlen.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

#[local] Abbreviation ASEGS := Asan.M.loaded_segments.

Definition asan_xstrlen_tab : xstrlen_tab :=
  {| xs_base := 0x5c57c; xs_rip := asan_rip_tab; xs_sl := asan_strlen_tab; xs_c_rsl := 0x101030;
     xs_g_cf := 0xff260; xs_p_cf := 0x1990a8; xs_c_inited := 0x108258 |}.

Section FPGen1.
Context {fx : FPState}.

Ltac lit a v := replace (at_ (0x5c57c : word) a) with v by (apply bv_eq; vm_compute; reflexivity).

(* [comment removed for export] *)
Lemma asan_inited_run : asan_inited_call ASEGS (0x74cac : word) 0x108258.
Proof using.
  intros regs mem rom ra Rd Hret H1.
  (chain_step; [ reflexivity | eapply step_auipc; [exact F_74ca4 | reflexivity | exact D_74ca4] | step_simpl ]).
  gres; imm_norm; vals_lit.
  (chain_step;
   [ reflexivity
   | eapply step_lb; [exact F_74ca8 | reflexivity | exact D_74ca8 | ];
     gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit; rdn_lit_exact Rd
   | step_simpl ]).
  gres. try rewrite (v_lb_small (Z_to_bv 8 1)) by (vm_compute; reflexivity).
  afence F_74cac D_74cac.
  an F_74cb0 D_74cb0.                                   (* [comment removed for export] *)
  an F_74cb4 D_74cb4.                                   (* [comment removed for export] *)
  aret F_74cb8 D_74cb8 ra.                              (* [comment removed for export] *)
  rewrite ?regupd_regupd_same.
  lazymatch goal with |- msteps _ (mkst (regupd _ 10 ?v) _ _ _) _ =>
    replace v with (Z_to_bv 64 1 : word) by (apply bv_eq; vm_compute; reflexivity) end.
  wd_refl.
Qed.

(* [comment removed for export] *)
Lemma try_asan_init_run : try_asan_init_call ASEGS (0x75bbc : word) 0x108258.
Proof using.
  intros regs mem rom ra Rd Hret H1 Hc0 Hdisj H16 H64 Hstk.
  pose proof (u64_range (getr regs 2)) as Hspr.
  wd_eexists. split; [|split].
  - an F_75bb4 D_75bb4.                                 (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ (getr regs 2) (-8));
        [exact F_75bb8 | reflexivity | exact D_75bb8
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | eapply (store_ok_sub ASEGS mem (at_ (getr regs 2) (-16)) _ 16); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.                                (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply step_sd_at with (a := at_ (getr regs 2) (-16));
        [exact F_75bbc | reflexivity | exact D_75bbc
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | eapply store_ok_mono; [apply wbytes_grows|];
          eapply (store_ok_sub ASEGS mem (at_ (getr regs 2) (-16)) _ 16); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ]
      | step_simpl]; vn.                                (* [comment removed for export] *)
    change (wbytes _ _ _) with (tai_mem mem (getr regs 2) ra (getr regs 8)).
    (chain_step; [ reflexivity | eapply step_auipc; [exact F_75bc0 | reflexivity | exact D_75bc0] | step_simpl ]).
    gres; imm_norm; vals_lit.
    an F_75bc4 D_75bc4.                                 (* [comment removed for export] *)
    chain_step; [reflexivity
      | eapply step_lb; [exact F_75bc8 | reflexivity | exact D_75bc8 | ];
        gres; imm_norm; (lazymatch goal with |- ?G => let G' := eval unfold v_auipc, v_addi in G in change_no_check G' end); vals_lit;
        lazymatch goal with |- rdn _ _ ?a _ = _ =>
          replace a with (Z_to_bv 64 0x108258 : word) by (apply bv_eq; vm_compute; reflexivity) end;
        (lazymatch goal with |- ?G => let G' := eval unfold tai_mem in G in change_no_check G' end); rewrite !rdn_wbytes_out;
          first [ exact Rd
                | (wd_lenlit; rewrite ?length_N_to_le_bytes; rewrite ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); wd_ulia) ]
      | step_simpl]; vn.                                (* [comment removed for export] *)
    try rewrite (v_lb_small (Z_to_bv 8 1)) by (vm_compute; reflexivity).
    an F_75bcc D_75bcc.                                 (* [comment removed for export] *)
    afence F_75bd0 D_75bd0.
    ab_ft F_75bd4 D_75bd4 ltac:(vals_lit; condz).      (* [comment removed for export] *)
    Ltac fld F D vv :=
      chain_step; [reflexivity
        | eapply step_ld with (bs := word_to_le_bytes 8 vv) (v := vv);
          [exact F | reflexivity | exact D
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; (lazymatch goal with |- ?G => let G' := eval unfold tai_mem in G in change_no_check G' end); rd8_chain
          | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
    fld F_75bd8 D_75bd8 ra.                             (* [comment removed for export] *)
    fld F_75bdc D_75bdc (getr regs 8).                  (* [comment removed for export] *)
    an F_75be0 D_75be0.                                 (* [comment removed for export] *)
    aret F_75be4 D_75be4 ra.                            (* [comment removed for export] *)
    lazymatch goal with |- msteps _ (mkst _ _ _ _) (mkst _ ?p _ _) => idtac end.
    wd_refl.
  - gres. apply bv_eq. vm_compute. reflexivity.
  - intros x X10 X11. gres.
    destruct (decide (x = 2)) as [->|N2]; [gres; rwH; rewrite ?at_addi; zlit_at; first [reflexivity | symmetry; apply at_0 | apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]] |].
    destruct (decide (x = 8)) as [->|N8]; [gres; reflexivity|].
    destruct (decide (x = 1)) as [->|N1]; [gres; symmetry; exact H1|].
    rewrite !getr_other by (first [exact N2 | exact N8 | exact N1 | exact X10 | exact X11 | (intros E; discriminate E)]). reflexivity.
Qed.

Lemma asan_xstrlen_tab_ok : xstrlen_tab_ok ASEGS asan_xstrlen_tab.
Proof using.
  split; (lazymatch goal with |- ?G => let G' := eval cbn [xs_base xs_rip xs_sl xs_c_rsl xs_g_cf xs_p_cf xs_c_inited asan_xstrlen_tab rt_base rt_m2s asan_rip_tab mt_g_shoff asan_m2s_tab_6fb04 st_base asan_strlen_tab] in G in change_no_check G' end).
  - (lazymatch goal with |- ?G => let G' := eval unfold xstrlen_words in G in change_no_check G' end). code_ato_vm.
  - exact asan_rip_tab_ok.
  - apply bv_eq; vm_compute; reflexivity.
  - exact asan_strlen_tab_ok.
  - apply ret_ok_even. vm_compute. reflexivity.
  - lit 100144%Z (0x74cac : word). exact asan_inited_run.
  - lit 104000%Z (0x75bbc : word). exact try_asan_init_run.
  - gload_tac F_5c5b0 D_5c5b0 F_5c5b4 D_5c5b4.
  - gload_tac F_5c5c8 D_5c5c8 F_5c5cc D_5c5cc.
  - lit 128%Z (0x5c5fc : word). gload_tac F_5c5f4 D_5c5f4 F_5c5f8 D_5c5f8.
  - lit 180%Z (0x5c630 : word). lit 400%Z (0x5c70c : word). eapply (gbnez_of ASEGS _ _ _ _ _ F_5c628 eq_refl D_5c628). apply bv_eq; vm_compute; reflexivity.
  - lit 452%Z (0x5c740 : word). lit 652%Z (0x5c808 : word). eapply (gbeqz_of ASEGS _ _ _ _ _ F_5c738 eq_refl D_5c738). apply bv_eq; vm_compute; reflexivity.
  - imm_norm. split; [vm_compute; reflexivity | lia].
Qed.


End FPGen1.
