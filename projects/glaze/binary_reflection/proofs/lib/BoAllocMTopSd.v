(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSecPh.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).

Section FPGen.
Context {fx : FPState}.

Section PH.
  Variables (M : word -> option byte) (FL MIDEND : Z).
  Hypothesis C_gsb : rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sb : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS M (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS M (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).

  Variables (addr size : Z) (ra fsp : word).
  Hypothesis Ha8 : addr mod 8 = 0.
  Hypothesis Hs8 : size mod 8 = 0.
  Hypothesis Hrng : (0x10007fff8000 <= addr /\ 8 <= size /\ addr + size <= 0x800000000000) \/ (0 <= addr /\ 8 <= size /\ addr + size <= 0x7fff7000).
  Hypothesis Hfsp : 2 ^ 32 + 64 <= U fsp /\ U fsp + 16 <= 2 ^ 47.
  Hypothesis Hstk : store_ok BSEGS M (at_ fsp (-64)) 64 = true.
  Hypothesis Hshw : store_ok BSEGS M (Z_to_bv 64 (0x7fff8000 + addr / 8)) (Z.to_nat (size / 8)) = true.
  Hypothesis Hret : ret_ok ra.

  Lemma ph_lits : 0 <= addr /\ addr + size <= 2 ^ 47 /\ 0 <= size.
  Proof using Hrng. destruct Hrng as [(A1 & A2 & A3) | (A1 & A2 & A3)]; lia. Qed.

  Ltac ph_common :=
    [> exact C_gsb | exact C_sb | exact C_gmb | exact C_mb | exact C_gme | exact C_me | exact C_ghe | exact C_he | exact C_grm
     | replace (word_to_le_bytes 8 (1033100 : word)) with (LE8 (Z_to_bv 64 0xfc38c)) by reflexivity; exact C_rm
     | vm_compute; discriminate
     | apply ret_ok_even; reflexivity
     | ..].

  Lemma mk_poisonH_fa : forall thr0,
    rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 1] ->
    poisonH BSEGS both_poison_tab M (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 250) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) thr0.
  Proof using Hret Hshw Hstk Hfsp Hrng Hs8 Ha8 C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sb C_gsb.
    intros thr0 C_cpm. pose proof ph_lits as (L1 & L2 & L3). destruct Hfsp as [F1 F2]. pose proof (u64_range fsp) as Hf.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
    all: ph_common.
    - intros _. split; [exact C_cpm | vm_compute; discriminate].
    - intros E0. exfalso. rewrite u_Z2bv in E0 by lia. lia.
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact Ha8.
    - rewrite u_Z2bv by lia. exact Hs8.
    - rewrite !u_Z2bv by lia. destruct Hrng as [(A1 & A2 & A3) | (A1 & A2 & A3)]; [left; lia | right; lia].
    - lia.
    - exact Hstk.
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia. replace (addr / 8 + 2147450880) with (0x7fff8000 + addr / 8) by lia. exact Hshw.
    - exact Hret.
  Qed.

  Lemma mk_poisonH_0 : forall CFL,
    rdn BSEGS M (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 CFL)) ->
    rdn BSEGS M (Z_to_bv 64 (CFL + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)) -> CFL = 0x19fce8 ->
    poisonH BSEGS both_poison_tab M (Z_to_bv 64 addr) (Z_to_bv 64 size) (Z_to_bv 64 0) ra fsp (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615.
  Proof using Hret Hshw Hstk Hfsp Hrng Hs8 Ha8 C_rm C_grm C_he C_ghe C_me C_gme C_mb C_gmb C_sb C_gsb.
    intros CFL C_gcf C_thr ECF. subst CFL. pose proof ph_lits as (L1 & L2 & L3). destruct Hfsp as [F1 F2]. pose proof (u64_range fsp) as Hf.
    split; (lazymatch goal with |- ?G => let G' := eval cbn [pt_base pt_mset pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
    all: ph_common.
    - intros NZ. exfalso. apply NZ. reflexivity.
    - intros _. split; [exact C_gcf|]. split; [replace (Z_to_bv 64 (1703144 + 120)) with (Z_to_bv 64 (0x19fce8 + 120) : word) by (apply bv_eq; reflexivity); exact C_thr|].
      (lazymatch goal with |- ?G => let G' := eval unfold shlen in G in change_no_check G' end). rewrite u_Z2bv by lia. split; [apply Z.div_lt_upper_bound; lia | lia].
    - (lazymatch goal with |- ?G => let G' := eval unfold poison_cells in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [pt_g_shoff pt_p_shoff pt_g_midbeg pt_p_midbeg pt_g_midend pt_p_midend pt_g_hiend pt_p_hiend pt_g_rms pt_p_rms pt_g_cfl pt_p_cfl pt_c_cpm both_poison_tab] in G in change_no_check G' end).
      repeat (constructor; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|]). constructor.
    - rewrite u_Z2bv by lia. exact Ha8.
    - rewrite u_Z2bv by lia. exact Hs8.
    - rewrite !u_Z2bv by lia. destruct Hrng as [(A1 & A2 & A3) | (A1 & A2 & A3)]; [left; lia | right; lia].
    - lia.
    - exact Hstk.
    - (lazymatch goal with |- ?G => let G' := eval unfold shad, shlen in G in change_no_check G' end). rewrite !u_Z2bv by lia. replace (addr / 8 + 2147450880) with (0x7fff8000 + addr / 8) by lia. exact Hshw.
    - exact Hret.
  Qed.
End PH.
End FPGen.
End BoAllocMSecPh.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSbRun1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA.BoAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s BoAllocMSecPh OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.
Local Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Lemma sb_shadow_arith2 : forall um n, um mod 4096 = 0 -> 0 <= um -> 64513 <= n ->
  forall k n8 nm re r8 asz a8, k = um / 8 -> n8 = n / 8 -> nm = n mod 8 -> re = sbre um n -> r8 = re / 8 -> asz = sbasz n -> a8 = asz / 8 ->
  (um = 8 * k /\ n = 8 * n8 + nm /\ 0 <= nm < 8 /\ asz = 8 * a8 /\ re = 8 * r8 /\ k + 256 + n8 <= r8 <= k + 256 + n8 + 1
   /\ n + 4096 <= asz <= n + 8198 /\ 0 <= k /\ r8 + 256 <= k + a8 /\ sec_needed n <= asz)
  /\ hideW (nm = 0 -> r8 = k + 256 + n8) /\ hideW (nm <> 0 -> r8 = k + 256 + n8 + 1)
  /\ ((um + asz) / 8 = k + a8 /\ (um + asz - re) / 8 = k + a8 - r8 /\ (um + asz - re) mod 8 = 0 /\ (um + 2048) / 8 = k + 256
      /\ (um + 2048) mod 8 = 0 /\ (um + 2048 + (n - nm)) / 8 = k + 256 + n8 /\ (n - nm) / 8 = n8 /\ (n - nm) mod 8 = 0 /\ um mod 8 = 0
      /\ re mod 8 = 0 /\ 2048 / 8 = 256).
Proof.
  intros um n Hum H0 Hn k n8 nm re r8 asz a8 -> -> -> -> -> -> ->. (lazymatch goal with |- ?G => let G' := eval unfold hideW, sbre, sbasz in G in change_no_check G' end). rewrite (rz_sec n) by lia.
  pose proof (sec_needed_bnd n ltac:(lia)) as Hs. set (sn := sec_needed n) in *. clearbody sn.
  Z.div_mod_to_equations; repeat split; lia.
Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Definition sb_foot1 (s um n z : Z) : Prop :=
  (um + 2040 <= z < um + 2048) \/ (s - 2336 <= z < s - 2272) \/ (SB + um / 8 <= z < SB + (um + sbasz n) / 8).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Ltac notinB := try (lazymatch goal with |- ?G => let G' := eval unfold poison_clob in G in change_no_check G' end); notin.
Ltac rchB := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with K : forall j : reg, In j _ -> getr r j = getr _ j |- _ => rewrite (K i) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]) end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notinB end end
                          | match goal with |- getr (regupd _ ?i _) ?i = _ => rewrite getr_same by (intros E; discriminate E) end
                          | match goal with |- getr (regupd _ ?j _) ?i = _ => rewrite getr_other by (intros E; discriminate E) end ]).

(* [comment removed for export] *)
Ltac slia0 B := clear - B; lia.
Ltac slia2 B X := clear - B X; lia.

Section RUNS1.
  Variables (M rom : word -> option byte) (r0 : bvmap 5 word).
  Variables (S m : word) (n id sbeg FL MIDEND : Z).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  Hypothesis H2 : getr r0 2 = sp2.
  Hypothesis H8 : getr r0 8 = Z_to_bv 64 0.
  Hypothesis H9 : getr r0 9 = Z_to_bv 64 n.
  Hypothesis H10 : getr r0 10 = Z_to_bv 64 id.
  Hypothesis H18 : getr r0 18 = m.
  Hypothesis H20 : getr r0 20 = at_ m (rz n).
  Hypothesis H21 : getr r0 21 = at_ m (rz n - 16).
  Hypothesis H22 : getr r0 22 = Z_to_bv 64 0x10ab58.
  Hypothesis H24 : getr r0 24 = Z_to_bv 64 0.
  Hypothesis H25 : getr r0 25 = at_ m (rz n + n).
  (* [comment removed for export] *)
  Hypothesis GS : 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47.
  Hypothesis Gn : 64513 <= n <= 2 ^ 34.
  Hypothesis Hid : 0 <= id < 2 ^ 32.
  Hypothesis Gm : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sbasz n <= U S - 3584 /\ U m + sbasz n + 4096 <= 2 ^ 47.
  Hypothesis Grng : hideW (U m + sbasz n <= 0x7fff7000 \/ 0x10007fff8000 <= U m - 4096).
  Hypothesis Gimg : hideW (U m + sbasz n <= AIMGLO \/ AIMGHI <= U m - 4096).
  Hypothesis Gsb : 0 <= sbeg /\ sbeg + 2 ^ 37 < 2 ^ 64.
  Hypothesis Dsb : U m < sbeg \/ sbeg + 2 ^ 37 <= U m.
  Hypothesis GFL : AIMGLO <= FL /\ FL + 4096 < AIMGHI.
  Hypothesis GME : 0 <= MIDEND < 2 ^ 64.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS M (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_gcf : rdn BSEGS M (Z_to_bv 64 0x105f08) 8 = Some (LE8 (Z_to_bv 64 0x19fce8)).
  Hypothesis C_thr64 : rdn BSEGS M (Z_to_bv 64 (0x19fce8 + 120)) 8 = Some (LE8 (Z_to_bv 64 18446744073709551615)).
  Hypothesis C_gsb : rdn BSEGS M (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sb : rdn BSEGS M (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 SB)).
  Hypothesis C_cpm : rdn BSEGS M (Z_to_bv 64 0x10da1c) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_gmb : rdn BSEGS M (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS M (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS M (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS M (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 (Z_to_bv 64 MIDEND)).
  Hypothesis C_ghe : rdn BSEGS M (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS M (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_gfl : rdn BSEGS M (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 FL)).
  Hypothesis C_pp : rdn BSEGS M (at_ (Z_to_bv 64 FL) 85) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_grm : rdn BSEGS M (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS M (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  (* [comment removed for export] *)
  Hypothesis C_sbeg : rdn BSEGS M (Z_to_bv 64 0x10ab78) 8 = Some (LE8 (Z_to_bv 64 sbeg)).
  Hypothesis C_pg : rdn BSEGS M (Z_to_bv 64 0x10ab98) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_sz : rdn BSEGS M (at_ m (-4080)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n))).
  (* [comment removed for export] *)
  Hypothesis C_hdr : store_ok BSEGS M (at_ m (rz n - 16)) 16 = true.
  Hypothesis C_shw : store_ok BSEGS M (Z_to_bv 64 (SB + U m / 8)) (Z.to_nat (sbasz n / 8)) = true.

  Theorem run_sB1 :
    exists (r5 : bvmap 5 word) (M5 : word -> option byte),
      msteps BSEGS (mkst r0 (Z_to_bv 64 0x4c940) M rom) (mkst r5 (Z_to_bv 64 0x4cae0) M5 rom)
      /\ (forall i : reg, In i [2; 3; 4; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr r5 i = getr r0 i)
      /\ (forall x : word, ~ sb_foot1 (U S) (U m) n (U x) -> M5 x = M x)
      /\ mem_grows M M5
      /\ rdn BSEGS M5 (at_ m (rz n - 8)) 8 = Some (LE8 (Z_to_bv 64 (0 * 2 ^ 32 + id)))
      /\ (forall x : word, SB + U m / 8 <= U x < SB + U m / 8 + 256 -> M5 x = Some (Z_to_bv 8 250))
      /\ (forall x : word, SB + sbre (U m) n / 8 <= U x < SB + (U m + sbasz n) / 8 -> M5 x = Some (Z_to_bv 8 250))
      /\ (forall x : word, SB + (U m + 2048) / 8 <= U x < SB + (U m + 2048) / 8 + n / 8 -> M5 x = Some (Z_to_bv 8 0))
      /\ (n mod 8 <> 0 -> M5 (Z_to_bv 64 (SB + (U m + 2048 + (n - n mod 8)) / 8)) = Some (Z_to_bv 8 (n mod 8))).
  Proof using C_shw C_hdr C_sz C_pg C_sbeg C_rm C_grm C_pp C_gfl C_he C_ghe C_me C_gme C_mb C_gmb C_cpm C_sb C_gsb C_thr64 C_gcf Hstk GME GFL Dsb Gsb Gimg Grng Gm Hid Gn GS H25 H24 H22 H21 H20 H18 H10 H9 H8 H2 MIDEND FL sbeg.
    pose proof (u64_range S) as HSr. pose proof (u64_range m) as Hmr.
    destruct GS as (GS1 & GS2). destruct Gm as (Gm1 & Gm2 & Gm3 & Gm4).
    set (k := U m / 8) in *. set (n8 := n / 8) in *. set (nm := n mod 8) in *.
    set (re := sbre (U m) n) in *. set (asz := sbasz n) in *. set (r8 := re / 8) in *. set (a8 := asz / 8) in *.
    destruct (sb_shadow_arith2 (U m) n Gm1 ltac:(lia) ltac:(lia) k n8 nm re r8 asz a8 eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl eq_refl)
      as (LIN & HZ & HNZ & IDS).
    destruct LIN as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10).
    destruct IDS as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I9 & I10 & I11).
    rewrite I1, I4, I6.
    assert (Erz : rz n = 2048) by (apply rz_sec; lia).
    assert (Gm' : U m mod 4096 = 0 /\ 8192 <= U m /\ U m + sec_needed n + 4096 <= 2 ^ 47) by (clear - Gm1 Gm2 Gm4 L10; lia).
    assert (Usp : U sp2 = U S - 2272) by (first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]).
    assert (BASE : (U m = 8 * k /\ n = 8 * n8 + nm /\ 0 <= nm < 8 /\ asz = 8 * a8 /\ re = 8 * r8 /\ k + 256 + n8 <= r8 <= k + 256 + n8 + 1
                    /\ n + 4096 <= asz <= n + 8198 /\ 0 <= k /\ r8 + 256 <= k + a8 /\ sec_needed n <= asz)
                   /\ 64513 <= n <= 2 ^ 34 /\ 8192 <= U m /\ U m + asz <= U S - 3584 /\ U m + asz + 4096 <= 2 ^ 47
                   /\ 0x7fff7f800000 <= U S - 3584 /\ U S + 16 <= 2 ^ 47 /\ U sp2 = U S - 2272 /\ 0 <= U S < 2 ^ 64 /\ 0 <= U m < 2 ^ 64 /\ rz n = 2048).
    { repeat split; first [assumption | apply L3 | apply L6 | apply L7 | apply Gn | apply HSr | apply Hmr]. }
    assert (RETA : forall d, d mod 2 = 0 -> 0 <= d < 2 ^ 24 -> ret_ok (at_ ARB d)).
    { clear. intros d Hd Hdr. pose proof ARB_ok as [E1 E2]. pose proof (u64_range ARB). apply ret_ok_at; [exact E1 | exact Hd | lia]. }
    (* [comment removed for export] *)
    assert (XF : forall (Mx : word -> option byte), (forall x : word, AIMGLO <= U x < AIMGHI -> Mx x = M x) ->
              forall (a : Z) (len : nat) bs, AIMGLO <= a -> a + Z.of_nat len <= AIMGHI ->
              rdn BSEGS M (Z_to_bv 64 a) len = Some bs -> rdn BSEGS Mx (Z_to_bv 64 a) len = Some bs).
    { clear. intros Mx IM a len bs Ha1 Ha2 Hr. eapply (rd_same BSEGS); [| | exact Hr]; [intros x Hx; apply IM; rewrite u_Z2bv in Hx by lia; lia | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]]. }
    assert (SOK64 : forall Mx : word -> option byte, mem_grows M Mx -> store_ok BSEGS Mx (at_ sp2 (-64)) 64 = true).
    { intros Mx GX. eapply store_ok_mono; [exact GX|]. rewrite at_at. (lazymatch goal with |- ?G => let G' := eval cbn [Z.add Z.opp Pos.add Z.pos_sub] in G in change_no_check G' end).
      eapply (store_ok_sub BSEGS M (at_ S (-3584)) _ 3584); [rewrite at_u; slia0 BASE | exact Hstk | rewrite !at_u by slia0 BASE; slia0 BASE | rewrite !at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE]. }
    assert (SOKsh : forall (Mx : word -> option byte) (o len : Z), mem_grows M Mx -> 0 <= o -> 0 <= len -> o + len <= a8 ->
              store_ok BSEGS Mx (Z_to_bv 64 (0x7fff8000 + (k + o))) (Z.to_nat len) = true).
    { intros Mx o len GX Ho Hl Hol. eapply store_ok_mono; [exact GX|]. unfold SB in C_shw.
      assert (Ha8 : 0 <= a8 /\ 0 <= k /\ 2147450880 + k + a8 < 2 ^ 63) by slia0 BASE.
      eapply (store_ok_sub BSEGS M (Z_to_bv 64 (2147450880 + k)) _ (Z.to_nat a8)); [rewrite u_Z2bv by (clear - Ha8; lia); rewrite Z2Nat.id by (clear - Ha8; lia); clear - Ha8; lia | exact C_shw
        | rewrite !u_Z2bv by (clear - Ha8 Ho Hl Hol; lia); clear - Ha8 Ho Hl Hol; lia | rewrite !u_Z2bv by (clear - Ha8 Ho Hl Hol; lia); rewrite !Z2Nat.id by (clear - Ha8 Ho Hl Hol; lia); clear - Ha8 Ho Hl Hol; lia]. }
    Ltac ximg XF IM C := (eapply (XF _ IM); [clear; lia | clear; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | exact C]).
    Ltac mkph L XF IM C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm :=
      apply L; [ ximg XF IM C_gsb | unfold SB in C_sb; ximg XF IM C_sb | ximg XF IM C_gmb | ximg XF IM C_mb | ximg XF IM C_gme | ximg XF IM C_me
       | ximg XF IM C_ghe | ximg XF IM C_he | ximg XF IM C_grm | ximg XF IM C_rm | .. ].
    (* [comment removed for export] *)
    destruct (amD1s BSEGS ARB both_HAL2 ARB_ok rom m n 0 Gn ltac:(lia) Gm' M r0 id sbeg Hid H10 H8 H9 H18 H20 H21 H22 H24 H25 C_hdr Gsb Dsb
                ltac:(unfold hideW in Gimg; slia2 BASE Gimg) C_sbeg C_pg C_sz)
      as (r1 & RUN1 & B1 & B10 & B11 & B12 & B8 & B22 & AG1).
    clear Dsb.
    set (M1 := amD_mem m n 0 M id) in *.
    assert (O1 : forall x : word, (U x < U m + 2040 \/ U m + 2048 <= U x) -> M1 x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1, amD_mem in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE | rewrite length_N_to_le_bytes, at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia2 BASE Hx]. }
    assert (G1 : mem_grows M M1) by ((lazymatch goal with |- ?G => let G' := eval unfold M1, amD_mem in G in change_no_check G' end); apply wbytes_grows).
    assert (R1 : rdn BSEGS M1 (at_ m (rz n - 8)) 8 = Some (LE8 (Z_to_bv 64 (0 * 2 ^ 32 + id)))).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1, amD_mem in G in change_no_check G' end). apply rdn_wbytes_hitw. rewrite at_u by slia0 BASE. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). slia0 BASE. }
    clearbody M1.
    assert (IMG1 : forall x : word, AIMGLO <= U x < AIMGHI -> M1 x = M x).
    { intros x Hx. apply O1. unfold hideW in Gimg. clear - Hx Gimg L7 Gn. lia. }
    (* [comment removed for export] *)
    assert (PH1 : poisonH BSEGS both_poison_tab M1 (Z_to_bv 64 (U m)) (Z_to_bv 64 2048) (Z_to_bv 64 250) (at_ ARB 0x4ca18) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0).
    { mkph (mk_poisonH_fa M1 MIDEND) XF IMG1 C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm.
      - exact I9.
      - reflexivity.
      - unfold hideW in Grng. slia2 BASE Grng.
      - slia0 BASE.
      - apply SOK64. exact G1.
      - rewrite I11. fold k. replace (2147450880 + k) with (2147450880 + (k + 0)) by lia. apply SOKsh; [exact G1 | lia | lia | slia0 BASE].
      - apply RETA; [reflexivity | lia].
      - ximg XF IMG1 C_cpm. }
    rewrite Z_to_bv_bv_unsigned in PH1.
    destruct (both_poison_shadow M1 rom m (Z_to_bv 64 2048) (Z_to_bv 64 250) (at_ ARB 0x4ca18) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0 r1
                PH1 B1 ltac:(rchB) B10 B11 B12) as (r2 & RUN2 & AG2).
    clear PH1.
    match type of RUN2 with msteps _ _ (mkst _ _ ?MM _) => set (M2 := MM) in * end.
    destruct (psm_facts M1 sp2 (at_ ARB 0x4ca18) (getr r1 8) (getr r1 9) (getr r1 18) (getr r1 19) (getr r1 20) (getr r1 21) (U m) 2048 250
                ltac:(slia0 BASE) ltac:(lia) ltac:(lia) ltac:(slia0 BASE)) as (O2 & N2 & G2).
    cbv zeta in O2, N2, G2. rewrite Z_to_bv_bv_unsigned in O2, N2, G2. change (psm M1 _ _ _ _ _ _ _ _ _ _ _) with M2 in O2, N2, G2.
    rewrite I11 in O2, N2. fold k in O2, N2. rewrite Usp in O2.
    clearbody M2.
    assert (GR2 : mem_grows M M2) by (eapply mem_grows_trans; [exact G1 | exact G2]).
    assert (FRo : forall x : word, AIMGLO <= U x < AIMGHI -> (U x < U S - 2272 - 56 \/ U S - 2272 <= U x) /\ (U x < 2147450880 + k \/ 2147450880 + k + a8 <= U x)).
    { intros x Hx. slia2 BASE Hx. }
    assert (IMG2 : forall x : word, AIMGLO <= U x < AIMGHI -> M2 x = M x).
    { intros x Hx. rewrite O2; [apply IMG1; exact Hx | exact (proj1 (FRo x Hx)) | destruct (proj2 (FRo x Hx)) as [X|X]; [left; exact X | right; slia2 BASE X]]. }
    (* [comment removed for export] *)
    destruct (amD1b BSEGS ARB both_HAL2 rom m n Gn Gm' M2 r2 ltac:(rchB) ltac:(rchB) ltac:(rchB)) as (r3 & RUN3 & C1 & C10 & C11 & C12 & AG3).
    fold re asz in C10, C11.
    assert (PH2 : poisonH BSEGS both_poison_tab M2 (Z_to_bv 64 re) (Z_to_bv 64 (U m + asz - re)) (Z_to_bv 64 250) (at_ ARB 0x4ca2c) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0).
    { mkph (mk_poisonH_fa M2 MIDEND) XF IMG2 C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm.
      - exact I10.
      - exact I3.
      - unfold hideW in Grng. slia2 BASE Grng.
      - slia0 BASE.
      - apply SOK64. exact GR2.
      - rewrite I2. fold r8. replace (2147450880 + r8) with (2147450880 + (k + (r8 - k))) by lia. apply SOKsh; [exact GR2 | | |]; slia0 BASE.
      - apply RETA; [reflexivity | lia].
      - ximg XF IMG2 C_cpm. }
    destruct (both_poison_shadow M2 rom (Z_to_bv 64 re) (Z_to_bv 64 (U m + asz - re)) (Z_to_bv 64 250) (at_ ARB 0x4ca2c) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 0 r3
                PH2 C1 ltac:(rchB) C10 C11 C12) as (r4 & RUN4 & AG4).
    clear PH2.
    match type of RUN4 with msteps _ _ (mkst _ _ ?MM _) => set (M3 := MM) in * end.
    destruct (psm_facts M2 sp2 (at_ ARB 0x4ca2c) (getr r3 8) (getr r3 9) (getr r3 18) (getr r3 19) (getr r3 20) (getr r3 21) re (U m + asz - re) 250
                ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE)) as (O3 & N3 & G3).
    cbv zeta in O3, N3, G3. change (psm M2 _ _ _ _ _ _ _ _ _ _ _) with M3 in O3, N3, G3.
    rewrite I2 in O3, N3. fold r8 in O3, N3. rewrite Usp in O3.
    clearbody M3.
    assert (GR3 : mem_grows M M3) by (eapply mem_grows_trans; [exact GR2 | exact G3]).
    assert (IMG3 : forall x : word, AIMGLO <= U x < AIMGHI -> M3 x = M x).
    { intros x Hx. rewrite O3; [apply IMG2; exact Hx | exact (proj1 (FRo x Hx)) | destruct (proj2 (FRo x Hx)) as [X|X]; [left; slia2 BASE X | right; slia2 BASE X]]. }
    (* [comment removed for export] *)
    destruct (amD1c BSEGS ARB both_HAL2 rom m n Gn M3 r4 ltac:(rchB)) as (r5 & RUN5 & D22 & AG5).
    destruct (amD2s BSEGS ARB both_HAL2 rom m n Gn Gm' M3 r5 ltac:(lia) D22 ltac:(rchB)) as (r6 & RUN6 & E1 & E10 & E11 & E12 & AG6).
    fold nm in D22, E11.
    assert (Ep : at_ m (rz n) = Z_to_bv 64 (U m + 2048)) by (rewrite Erz; reflexivity).
    assert (PH3 : poisonH BSEGS both_poison_tab M3 (Z_to_bv 64 (U m + 2048)) (Z_to_bv 64 (n - nm)) (Z_to_bv 64 0) (at_ ARB 0x4ca4c) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615).
    { mkph (fun a b c d e f g h i j ad sz ra fsp h1 h2 h3 h4 h5 h6 h7 => mk_poisonH_0 M3 MIDEND a b c d e f g h i j ad sz ra fsp h1 h2 h3 h4 h5 h6 h7 0x19fce8) XF IMG3 C_gsb C_sb C_gmb C_mb C_gme C_me C_ghe C_he C_grm C_rm.
      - exact I5.
      - exact I8.
      - unfold hideW in Grng. slia2 BASE Grng.
      - slia0 BASE.
      - apply SOK64. exact GR3.
      - rewrite I4, I7. apply SOKsh; [exact GR3 | | |]; slia0 BASE.
      - apply RETA; [reflexivity | lia].
      - ximg XF IMG3 C_gcf.
      - ximg XF IMG3 C_thr64.
      - reflexivity. }
    rewrite <- Ep in PH3.
    destruct (both_poison_shadow M3 rom (at_ m (rz n)) (Z_to_bv 64 (n - nm)) (Z_to_bv 64 0) (at_ ARB 0x4ca4c) sp2 (Z_to_bv 8 1) (Z_to_bv 64 MIDEND) 18446744073709551615 r6
                PH3 E1 ltac:(rchB) E10 E11 E12) as (r7 & RUN7 & AG7).
    clear PH3.
    match type of RUN7 with msteps _ _ (mkst _ _ ?MM _) => set (M4 := MM) in * end.
    destruct (psm_facts M3 sp2 (at_ ARB 0x4ca4c) (getr r6 8) (getr r6 9) (getr r6 18) (getr r6 19) (getr r6 20) (getr r6 21) (U m + 2048) (n - nm) 0
                ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE) ltac:(slia0 BASE)) as (O4 & N4 & G4).
    cbv zeta in O4, N4, G4. rewrite <- Ep in O4, N4, G4. change (psm M3 _ _ _ _ _ _ _ _ _ _ _) with M4 in O4, N4, G4.
    rewrite I4, I7 in O4, N4. rewrite Usp in O4.
    clearbody M4.
    assert (GR4 : mem_grows M M4) by (eapply mem_grows_trans; [exact GR3 | exact G4]).
    assert (IMG4 : forall x : word, AIMGLO <= U x < AIMGHI -> M4 x = M x).
    { intros x Hx. rewrite O4; [apply IMG3; exact Hx | exact (proj1 (FRo x Hx)) | destruct (proj2 (FRo x Hx)) as [X|X]; [left; slia2 BASE X | right; slia2 BASE X]]. }
    (* [comment removed for export] *)
    assert (K7 : forall i : reg, In i [2; 3; 4; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr r7 i = getr r0 i).
    { intros i Hi. cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [rewrite (AG7 _) by notinB; rewrite (AG6 _) by notinB; rewrite (AG5 _) by notinB; rewrite (AG4 _) by notinB;
                                       rewrite (AG3 _) by notinB; rewrite (AG2 _) by notinB; rewrite (AG1 _) by notinB; reflexivity|]). destruct Hi. }
    assert (F22 : getr r7 22 = Z_to_bv 64 (n - nm)) by (rewrite (AG7 _) by notinB; rewrite (AG6 _) by notinB; exact D22).
    assert (W8 : exists (r8' : bvmap 5 word) (M5 : word -> option byte),
               msteps BSEGS (mkst r7 (at_ ARB 0x4ca4c) M4 rom) (mkst r8' (at_ ARB 0x4cae0) M5 rom)
               /\ (forall i : reg, In i [2; 3; 4; 9; 18; 19; 20; 21; 23; 24; 26; 27]%bv -> getr r8' i = getr r7 i)
               /\ (forall x : word, (nm = 0 \/ U x <> 2147450880 + (k + 256 + n8)) -> M5 x = M4 x)
               /\ mem_grows M4 M5
               /\ (nm <> 0 -> M5 (Z_to_bv 64 (2147450880 + (k + 256 + n8))) = Some (Z_to_bv 8 nm) /\ r8 = k + 256 + n8 + 1)).
    { destruct (Z.eq_dec nm 0) as [Em|Em].
      - exists r7, M4. split; [| split; [intros; reflexivity | split; [intros; reflexivity | split; [apply mem_grows_refl | intros X; exfalso; exact (X Em)]]]].
        apply (amE1zs BSEGS ARB both_HAL2 rom m n Gn M4 r7 Em); [rewrite (K7 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H9 | exact F22].
      - destruct (amE1s BSEGS ARB both_HAL2 ARB_ok rom m n Gn Gm' 0x105f18 (Z_to_bv 64 0x10e1b8) SB
                    ltac:((lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); split; [lia | fold k; slia0 BASE])
                    0x10da1c 0x105f20 0x105f28 0x105f30 0x105f10 (Z_to_bv 64 0x10eea8) (Z_to_bv 64 0x10eeb0) (Z_to_bv 64 0x10eea0) (Z_to_bv 64 FL) (Z_to_bv 64 MIDEND)
                    both_CPM both_GCPM both_GLSB2 both_GLMB both_GLME both_GLHE both_GLFL
                    ltac:(split; [repeat constructor; lia | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ]]) M4 r7
                    ltac:(unfold hideW in Grng; (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end); slia2 BASE Grng) Em
                    ltac:(rewrite (K7 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H9) F22 ltac:(rewrite (K7 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H20))
          as (r8' & RUN8 & AG8).
        { ximg XF IMG4 C_cpm. } { ximg XF IMG4 C_gsb. } { ximg XF IMG4 C_sb. } { ximg XF IMG4 C_gmb. } { ximg XF IMG4 C_mb. }
        { ximg XF IMG4 C_gme. } { ximg XF IMG4 C_me. } { ximg XF IMG4 C_ghe. } { ximg XF IMG4 C_he. } { ximg XF IMG4 C_gfl. }
        { assert (UFL : U (Z_to_bv 64 FL) = FL) by (apply u_Z2bv; clear - GFL; lia).
          eapply (rd_same BSEGS); [| | exact C_pp]; [intros x Hx; apply IMG4; rewrite at_u in Hx by (rewrite UFL; clear - GFL; lia); rewrite UFL in Hx; cbn in Hx; clear - Hx GFL; lia
                                                     | rewrite at_u by (rewrite UFL; clear - GFL; lia); rewrite UFL; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GFL; lia]. }
        { rewrite Erz. fold nm. rewrite I6. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). replace (2147450880 + (k + 256 + n8)) with (2147450880 + (k + (256 + n8))) by lia.
          change 1%nat with (Z.to_nat 1). apply SOKsh; [exact GR4 | slia0 BASE | lia | unfold hideW in HNZ; specialize (HNZ Em); slia0 BASE]. }
        exists r8', (amE1_mem m n SB M4). split; [exact RUN8|].
        assert (EA : Z_to_bv 64 (SB + (U m + rz n + (n - n mod 8)) / 8) = Z_to_bv 64 (2147450880 + (k + 256 + n8)) :> word).
        { rewrite Erz. fold nm. rewrite I6. reflexivity. }
        split; [intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [rewrite (AG8 _) by notinB; reflexivity|]); destruct Hi|].
        (lazymatch goal with |- ?G => let G' := eval unfold amE1_mem in G in change_no_check G' end). rewrite EA. split; [| split; [apply wbytes_grows|]].
        + intros x [Hx|Hx]; [exfalso; exact (Em Hx)|]. apply wbytes_outside; [(lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; slia0 BASE | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
        + intros _. split; [| unfold hideW in HNZ; exact (HNZ Em)].
          rewrite wbytes_inside; [| (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; slia0 BASE | (lazymatch goal with |- ?G => let G' := eval cbn [length] in G in change_no_check G' end); rewrite u_Z2bv by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
          rewrite Z.sub_diag. reflexivity. }
    destruct W8 as (r8' & M5 & RUN8 & K8 & O5 & G5 & N5).
    (* [comment removed for export] *)
    exists r8', M5.
    assert (C250 : cbyte (Z_to_bv 64 250) = Z_to_bv 8 250) by (apply bv_eq; reflexivity).
    assert (C0 : cbyte (Z_to_bv 64 0) = Z_to_bv 8 0) by (apply bv_eq; reflexivity).
    (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end). split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]].
    - rewrite <- (ARB_lit 0x4c940) by lia. rewrite <- (ARB_lit 0x4cae0) by lia.
      rewrite (ARB_lit 0x70080) in RUN1, RUN3, RUN6 by lia.
      replace (458880%bv : word) with (Z_to_bv 64 458880 : word) in RUN2, RUN4, RUN7 by (apply bv_eq; reflexivity).
      eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. exact RUN8.
    - intros i Hi. rewrite (K8 i Hi). apply K7. exact Hi.
    - intros x NF. unfold sb_foot1, SB in NF. fold asz in NF. rewrite I1 in NF. fold k in NF.
      assert (Q1 : U x < U m + 2040 \/ U m + 2048 <= U x) by (clear - NF; lia).
      assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (clear - NF; lia).
      assert (Q3 : U x < 2147450880 + k \/ 2147450880 + (k + a8) <= U x) by (clear - NF; lia).
      rewrite O5 by (right; destruct Q3 as [Q3|Q3]; [slia2 BASE Q3 | clear - Q3 L6 L9 L2 L3 Gn; lia]).
      rewrite O4; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O3; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O2; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      apply O1. exact Q1.
    - eapply mem_grows_trans; [exact GR4 | exact G5].
    - eapply (rd_same BSEGS); [| | exact R1]; [| rewrite at_u by slia0 BASE; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); slia0 BASE].
      intros x Hx. rewrite at_u in Hx by slia0 BASE. rewrite Erz in Hx. cbn in Hx.
      assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (left; slia2 BASE Hx).
      assert (Q3 : U x < 2147450880 + k \/ 2147450880 + (k + a8) <= U x).
      { unfold hideW in Grng. destruct Grng as [G|G]; [left | right]; clear - G Hx L1 L4 L7 L8 Gn Gm2 Gm4; lia. }
      rewrite O5 by (right; destruct Q3 as [Q3|Q3]; [slia2 BASE Q3 | slia2 BASE Q3]).
      rewrite O4; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O3; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      rewrite O2; [| exact Q2 | destruct Q3 as [Q3|Q3]; [left; slia2 BASE Q3 | right; slia2 BASE Q3]].
      reflexivity.
    - intros x Hx. assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (left; slia2 BASE Hx).
      rewrite O5 by (right; slia2 BASE Hx). rewrite O4; [| exact Q2 | left; slia2 BASE Hx]. rewrite O3; [| exact Q2 | left; slia2 BASE Hx].
      rewrite <- C250. apply N2. slia2 BASE Hx.
    - fold re r8 k. intros x Hx. assert (Q2 : U x < U S - 2272 - 56 \/ U S - 2272 <= U x) by (left; slia2 BASE Hx).
      rewrite O5; [| destruct (Z.eq_dec nm 0) as [Em|Em]; [left; exact Em | right; unfold hideW in HNZ; specialize (HNZ Em); clear - Hx HNZ; lia]].
      rewrite O4; [| exact Q2 | right; slia2 BASE Hx].
      rewrite <- C250. apply N3. slia2 BASE Hx.
    - intros x Hx. rewrite O5 by (right; slia2 BASE Hx). rewrite <- C0. apply N4. slia2 BASE Hx.
    - intros Em. exact (proj1 (N5 Em)).
  Qed.
End RUNS1.
End FPGen.
End BoAllocMSbRun1.
Require LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSecDefs.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)
Definition sec_hx (mp n a : Z) : Prop :=
  let p := mp + sec_user_off n in
  a = p - 16
  \/ (mp + PG <= a < mp + PG + 16)
  \/ (SB + (mp + PG) / 8 <= a < SB + p / 8)
  \/ (SB + (p + n + 7) / 8 <= a < SB + (mp + sec_map_size n) / 8).

Lemma mmap_except_vm : forall a n m, same_except_vm m (mmap_model a n m).
Proof. intros a n [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.

Section WithCeil.
Context {RC : run_ceil}.

Section SECDEFS.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  #[local] Abbreviation T := (bt_thread bt).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition runS_st (st : ast) (mp n : Z) (grow : bool) (d' : depot) (naa' : list (Z * Z)) : ast :=
    depot_st (op_sec_alloc (op_meter st EVT [] 0) mp n grow) d' naa'.

  (* [comment removed for export] *)
  Definition runS_post (st : ast) (Lc FF : list (Z * Z)) (R : bvmap 5 word) (M : mem) (mdl : Model) (n : Z) (c' : config) : Prop :=
    exists fx' (R' : bvmap 5 word) (M' M0 : mem) (mdl' : Model) (mp : Z) (grow : bool) (d' : depot) (naa' : list (Z * Z))
           (id : Z) (x18 x19 : word),
      let S := getr R 2 in
      let p := mp + sec_user_off n in
      let st' := runS_st st mp n grow d' naa' in
      c' = mkCfg (@mkst fx' R' (Z_to_bv 64 0x4c940) M' (seg_rom BSEGS)) mdl'
      /\ FXOK fx' /\ m_halted mdl' = None /\ BackingAlgebra.model_ivs_wf mdl'
      /\ WF bt st' ((p, n) :: Lc) FF /\ Rep bt st' ((p, n) :: Lc) FF M0 mdl'
      (* [comment removed for export] *)
      /\ mp mod PG = 0 /\ dyn_ok (bt_ia bt) mp (mp + sec_map_size n)
      /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> mp + sec_map_size n <= lo \/ hi <= mp)
      /\ range_allowed (a_aa st') (sh_lo mp) (sh_hi mp (sec_map_size n))
      (* [comment removed for export] *)
      /\ (forall a : word, M' a <> M0 a -> sec_hx mp n (U a) /\ M' a <> None)
      (* [comment removed for export] *)
      /\ (forall a : word, M' a <> M a ->
            ((U S - 3584 <= U a < U S) \/ rt_priv (bt_ia bt) Lc FF (U a) \/ in_wins (ia_priv (bt_ia bt)) (U a)) /\ M' a <> None)
      (* [comment removed for export] *)
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
             rdn BSEGS M' (at_ S k0) 8 = Some (LE8 v))
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
             rdn BSEGS M' (at_ S k0) 8 = Some (LE8 v))
      /\ (forall a : word, U S - MSTK_A <= U a < U S -> M' a <> None /\ store_ok BSEGS M' a 1%nat = true)
      (* [comment removed for export] *)
      (* [comment removed for export] *)
      /\ getr R' 2 = at_ S (-2272) /\ getr R' 4 = getr R 4 /\ getr R' 3 = getr R 3
      /\ getr R' 8 = Z_to_bv 64 0 /\ getr R' 9 = Z_to_bv 64 n /\ getr R' 10 = Z_to_bv 64 id /\ getr R' 18 = Z_to_bv 64 (mp + PG)
      /\ getr R' 19 = Z_to_bv 64 (sec_needed n) /\ getr R' 20 = Z_to_bv 64 p /\ getr R' 21 = Z_to_bv 64 (p - 16)
      /\ getr R' 22 = Z_to_bv 64 0x10ab58 /\ getr R' 23 = at_ S (-2128) /\ getr R' 24 = Z_to_bv 64 0
      /\ getr R' 25 = Z_to_bv 64 (p + n) /\ getr R' 26 = Z_to_bv 64 T /\ getr R' 27 = Z_to_bv 64 1
      /\ 0 <= id < 2 ^ 32
      /\ same_except_vm mdl mdl'
      /\ lazy_kept (bt_ia bt) Lc FF mdl mdl'.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition sec_frames (fx : FPState) (R : bvmap 5 word) (n : Z) (rq : bvmap 5 word) (Mq : mem) : Prop :=
    exists (x18 x19 : word) (sz : Z) (bsz : list byte),
      let S := getr R 2 in
      la_regs (at_ S (-2320)) (Z_to_bv 64 0x10ae08) (sec_needed n) rq /\ getr rq 21 = Z_to_bv 64 8
      /\ getr rq 4 = getr R 4 /\ getr rq 3 = getr R 3 /\ getr rq 26 = Z_to_bv 64 T /\ getr rq 27 = Z_to_bv 64 1
      /\ (forall (k0 : Z) (v : word), In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
             rdn BSEGS Mq (at_ S k0) 8 = Some (LE8 v))
      /\ (forall (k0 : Z) (v : word),
             In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
             rdn BSEGS Mq (at_ S k0) 8 = Some (LE8 v))
      /\ rdn BSEGS Mq (at_ S (-2120)) 4 = Some (LE4 sz) /\ rdn BSEGS Mq (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat /\ (1 <= sz <= 8 /\ bytes_le_to_Z bsz = sz)
      /\ rdn BSEGS Mq (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (o : Z) (v : word),
             In (o, v) [(-8, Z_to_bv 64 0x4c834); (-16, Z_to_bv 64 0); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048)]%Z ->
             rdn BSEGS Mq (at_ (at_ S (-2272)) o) 8 = Some (LE8 v))
      /\ (forall (o : Z) (v : word),
             In (o, v) [(-8, Z_to_bv 64 0x50d94); (-16, Z_to_bv 64 8); (-24, Z_to_bv 64 n); (-32, Z_to_bv 64 8); (-40, Z_to_bv 64 (sec_needed n)); (-48, Z_to_bv 64 2048);
                        (-56, Z_to_bv 64 n); (-64, Z_to_bv 64 0x10ab58); (-72, at_ S (-2128)); (-80, Z_to_bv 64 18446744073709551608); (-88, Z_to_bv 64 7)]%Z ->
             rdn BSEGS Mq (at_ (at_ S (-2320)) o) 8 = Some (LE8 v))
      /\ (forall a : word, U S - MSTK_A <= U a < U S -> Mq a <> None /\ store_ok BSEGS Mq a 1%nat = true).

  (* [comment removed for export] *)
  Definition at_sec_null (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (n : Z) (st : ast) (c' : config) : Prop :=
    exists (rq : bvmap 5 word) (Mq : mem) (mdlq : Model),
      let S := getr R 2 in
      c' = mkCfg (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS)) mdlq
      /\ m_halted mdlq = None /\ BackingAlgebra.model_ivs_wf mdlq
      /\ Rep bt st Lc FF Mq mdlq
      /\ getr rq 10 = Z_to_bv 64 0 /\ sec_frames fx R n rq Mq
      /\ (forall a : word, Mq a <> M a -> U S - 2736 <= U a < U S)
      /\ same_except_vm mdl mdlq /\ lazy_kept (bt_ia bt) Lc FF mdl mdlq.

  (* [comment removed for export] *)
  Definition at_sec_grant (fx : FPState) (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (n : Z) (st : ast) (c' : config) : Prop :=
    exists (rq : bvmap 5 word) (Mq : mem) (mdlq : Model) (a : word),
      let S := getr R 2 in
      let msz := sec_map_size n in
      c' = mkCfg (@mkst fx rq (Z_to_bv 64 0x51080) Mq (seg_rom BSEGS)) mdlq
      /\ AsKSys10.chunk_child mdl mdlq a (Z_to_bv 64 msz) /\ MInv (a_aa st) mdlq
      /\ dyn_ok (bt_ia bt) (U a) (U a + msz) /\ U a mod PG = 0
      /\ (forall lo hi, In (lo, hi) (all_ranges bt st) -> U a + msz <= lo \/ hi <= U a)
      /\ (forall b0 n0, In (b0, n0) (bt_maps0 bt) -> U a + msz <= U b0 \/ U b0 + U n0 <= U a)
      /\ getr rq 10 = a /\ sec_frames fx R n rq Mq
      /\ (forall x : word, Mq x <> M x -> (U S - 2736 <= U x < U S) \/ (U a <= U x < U a + msz))
      /\ (forall x : word, U a <= U x < U a + msz -> Mq x = Some (Z_to_bv 8 0))
      /\ mem_grows M Mq
      /\ same_except_vm mdl mdlq.

  (* [comment removed for export] *)
  Definition partBs_stmt (HPf : option Z -> ast -> Prop) : Prop :=
    forall (h : option Z) fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret n sp : Z) (st : ast) (c' : config),
      m_halted mdl = None -> FXOK fx ->
      WF bt st Lc FF -> bounds st Lc B C K -> HPf h st -> hole_ok h n ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A ->
      U (getr R 10) = n -> 64512 < n <= NMAX -> fpc M (U (getr R 8)) sp DMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      (forall st', (forall c, a_reg st' c = a_reg st c /\ a_cache st' c = a_cache st c) -> a_kact st' = a_kact st + kcost_malloc n -> HPf None st') ->
      runS_post st Lc FF R M mdl n c' ->
      katD BSEGS c' (malloc_ok BSEGS FXOK both_addrs (fun h0 => AAINVP (HPf h0) bt) MSTK_A R M mdl Lc FF B C K ret n sp).
End SECDEFS.
End WithCeil.
End BoAllocMSecDefs.
Require Stdlib.NArith.NArith OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocMSecK.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.Fs LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Monad LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.Common.AllocSim OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvLedger OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2.

Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Open Scope Z_scope.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation BSEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Lemma la_msz_sec : forall n, la_msz (sec_needed n) = sec_map_size n.
Proof. intros n. (lazymatch goal with |- ?G => let G' := eval unfold la_msz, sec_map_size, RoundUp, PG in G in change_no_check G' end). f_equal. f_equal. f_equal. lia. Qed.

Lemma sec_msz_bnd : forall n, 64512 < n -> sec_map_size n mod 4096 = 0 /\ n + 8192 <= sec_map_size n <= n + 12294.
Proof.
  intros n Hn. pose proof (sec_needed_bnd n Hn) as B. rewrite <- la_msz_sec. (lazymatch goal with |- ?G => let G' := eval unfold la_msz in G in change_no_check G' end).
  pose proof (Z.div_mod (sec_needed n + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sec_needed n + 4095) 4096 ltac:(lia)).
  split; [rewrite Z.add_comm, Z.mul_comm; rewrite <- (Z.mul_1_r 4096) at 1; rewrite <- Z.mul_add_distr_l, Z.mul_comm; apply Z_mod_mult | lia].
Qed.


(* [comment removed for export] *)
Lemma zfill_in_s : forall (a n : word) m (x : word),
  bv_unsigned a <= bv_unsigned x < bv_unsigned a + bv_unsigned n -> zfill a n m x = Some (Z_to_bv 8 0).
Proof.
  intros a n m x Hx. (lazymatch goal with |- ?G => let G' := eval unfold zfill, AllocSim.zmem in G in change_no_check G' end).
  rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.ltb_lt _ _)) by lia. reflexivity.
Qed.
Lemma zfill_grows_s : forall (a n : word) (Mb : word -> option byte), mem_grows Mb (zfill a n Mb).
Proof. intros a n Mb x Hx. (lazymatch goal with |- ?G => let G' := eval unfold zfill, AllocSim.zmem in G in change_no_check G' end). destruct (_ && _)%bool; [discriminate | exact Hx]. Qed.

(* [comment removed for export] *)
Abbreviation sec_shs := sec_hull.

Lemma sec_naa_bytes : forall mp n, A_bytes (sec_naa mp n) = sec_hull mp n.
Proof. intros mp n. (lazymatch goal with |- ?G => let G' := eval unfold sec_naa, sec_hull in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes fst snd] in G in change_no_check G' end). lia. Qed.

Lemma sec_shs_bnd : forall mp n, 0 <= mp -> 64512 < n -> 0 <= sec_hull mp n <= n / 8 + 9730.
Proof.
  intros mp n Hmp Hn. destruct (sec_msz_bnd n Hn) as [M1 M2]. (lazymatch goal with |- ?G => let G' := eval unfold sec_hull, sec_hull_lo, sec_hull_hi, pgup, pgdn, PG, sh_hi, sh_lo, SB in G in change_no_check G' end).
  replace (4096 - 1) with 4095 by reflexivity.
  pose proof (Z.div_mod (0x7fff8000 + mp / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (0x7fff8000 + mp / 8) 4096 ltac:(lia)).
  pose proof (Z.div_mod (0x7fff8000 + (mp + sec_map_size n + 7) / 8 + 4095) 4096 ltac:(lia)).
  pose proof (Z.mod_pos_bound (0x7fff8000 + (mp + sec_map_size n + 7) / 8 + 4095) 4096 ltac:(lia)).
  pose proof (Z.div_mod mp 8 ltac:(lia)). pose proof (Z.mod_pos_bound mp 8 ltac:(lia)).
  pose proof (Z.div_mod (mp + sec_map_size n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (mp + sec_map_size n + 7) 8 ltac:(lia)).
  pose proof (Z.div_mod n 8 ltac:(lia)). pose proof (Z.mod_pos_bound n 8 ltac:(lia)).
  lia.
Qed.
Lemma sec_naa_wf : forall A mp n, A_wf A -> 0 <= mp -> 64512 < n -> A_wf (A ++ sec_naa mp n).
Proof.
  intros A mp n AW Hmp Hn. (lazymatch goal with |- ?G => let G' := eval unfold sec_naa, sec_hull_lo, sec_hull_hi, pgup, pgdn in G in change_no_check G' end). apply A_wf_snoc; [exact AW | | apply Z_mod_mult | apply Z_mod_mult].
  pose proof (sec_shs_bnd mp n Hmp Hn) as B. unfold sec_hull, sec_hull_lo, sec_hull_hi, pgup, pgdn in B. lia.
Qed.
Lemma sec_naa_allowed : forall A mp n, 0 <= mp -> mp + sec_map_size n <= 2 ^ 47 -> 64512 < n ->
  range_allowed (A ++ sec_naa mp n) (sh_lo mp) (sh_hi mp (sec_map_size n)).
Proof.
  intros A mp n Hmp Hhi Hn a Ha. destruct (sec_msz_bnd n Hn) as [M1 M2].
  assert (Ra : 0 <= a < 2 ^ 64).
  { unfold sh_lo, sh_hi, SB in Ha. pose proof (Z.div_mod mp 8 ltac:(lia)). pose proof (Z.mod_pos_bound mp 8 ltac:(lia)).
    pose proof (Z.div_mod (mp + sec_map_size n + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (mp + sec_map_size n + 7) 8 ltac:(lia)). lia. }
  (lazymatch goal with |- ?G => let G' := eval unfold page_allowedb in G in change_no_check G' end). apply existsb_exists. exists (sh_lo mp / 4096 * 4096, (sh_hi mp (sec_map_size n) + 4095) / 4096 * 4096).
  split; [apply in_app_iff; right; left; (lazymatch goal with |- ?G => let G' := eval unfold sec_hull_lo, sec_hull_hi, pgup, pgdn, PG in G in change_no_check G' end); replace (4096 - 1) with 4095 by reflexivity; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval cbn [fst snd] in G in change_no_check G' end).
  pose proof (page_base_le3 (Z_to_bv 64 a)) as (P1 & P2 & P3). rewrite u_Z2bv in P1, P2 by lia. unfold page_size in *.
  pose proof (Z.div_mod (sh_lo mp) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sh_lo mp) 4096 ltac:(lia)).
  pose proof (Z.div_mod (sh_hi mp (sec_map_size n) + 4095) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (sh_hi mp (sec_map_size n) + 4095) 4096 ltac:(lia)).
  pose proof (Z.div_mod (U (page_base (Z_to_bv 64 a))) 4096 ltac:(lia)).
  apply andb_true_intro. split; [apply Z.leb_le | apply Z.leb_le].
  - (* [comment removed for export] *)
    assert (Q : sh_lo mp / 4096 <= U (page_base (Z_to_bv 64 a)) / 4096).
    { apply Z.div_le_lower_bound; [lia|]. rewrite P3 in *. lia. }
    rewrite P3 in *. lia.
  - assert (Q : U (page_base (Z_to_bv 64 a)) / 4096 + 1 <= (sh_hi mp (sec_map_size n) + 4095) / 4096).
    { apply Z.div_le_lower_bound; [lia|]. rewrite P3 in *. lia. }
    rewrite P3 in *. lia.
Qed.


(* [comment removed for export] *)
Lemma sec_flags_clear : forall h n st, holes_le h st -> hole_ok h n -> 64512 < n ->
  forall c, r_uhole (a_reg st c) = false /\ r_fhole (a_reg st c) = false.
Proof.
  intros h n st HL HO Hn c.
  assert (NF : ~ (r_uhole (a_reg st c) = true \/ r_fhole (a_reg st c) = true)).
  { intros F. destruct (HL c F) as (n' & E & Hn' & _). destruct HO as [HO | HO]; rewrite HO in E; [discriminate E | injection E as <-; lia]. }
  split; [destruct (r_uhole (a_reg st c)); [exfalso; apply NF; left; reflexivity | reflexivity]
         | destruct (r_fhole (a_reg st c)); [exfalso; apply NF; right; reflexivity | reflexivity]].
Qed.
Lemma sec_holes_none : forall h n st st', holes_le h st -> hole_ok h n -> 64512 < n -> (forall c, a_reg st' c = a_reg st c) -> holes_le None st'.
Proof.
  intros h n st st' HL HO Hn ER c F. exfalso. rewrite ER in F. destruct (sec_flags_clear h n st HL HO Hn c) as [F1 F2].
  destruct F as [F | F]; [rewrite F1 in F | rewrite F2 in F]; discriminate F.
Qed.
Lemma sec_no_holes : forall {RC : run_ceil} bt h n st, holes_le h st -> hole_ok h n -> 64512 < n -> forall z, ~ holes bt st z.
Proof.
  intros RC bt h n st HL HO Hn z (c & _ & [[F _] | [F _]]); destruct (sec_flags_clear h n st HL HO Hn c) as [F1 F2];
    [rewrite F1 in F | rewrite F2 in F]; discriminate F.
Qed.

Section SecK.
  Context {RUN : run_ceil}.
  Variable bt : as_boot.

  (* [comment removed for export] *)
  Theorem sec_pre_budget : forall st Lc FF M0 mdl (B C K n mp : Z),
    Rep bt st Lc FF M0 mdl -> WF bt st Lc FF -> bounds st Lc B C K ->
    64512 < n -> B + (n + MBLK) <= GBUDGET -> K + kcost_malloc n <= KCAP -> 0 <= mp ->
    eager_used mdl + sec_map_size n + 2 ^ 17 + A_bytes (a_aa st) + sec_hull mp n <= vm_limit (m_vmmaps mdl).
  Proof using.
    intros st Lc FF M0 mdl B C K n mp R W (BP & _ & BK) Hn HB HK Hmp.
    destruct (sec_msz_bnd n Hn) as [M1 M2]. pose proof (sec_hull_le mp n Hmp ltac:(lia)) as HL.
    pose proof (budget_core bt st Lc FF (2 ^ 20) (2 ^ 28) W (n + MBLK) 1 ltac:((lazymatch goal with |- ?G => let G' := eval unfold MBLK in G in change_no_check G' end); lia) ltac:(lia)
                  ltac:((lazymatch goal with |- ?G => let G' := eval unfold QCAP in G in change_no_check G' end); lia) ltac:(unfold kcost_malloc in HK; lia)) as BR.
    destruct (ledger_R bt st Lc FF M0 mdl R) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & LIM & _).
    destruct R as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & _ & _ & _ & _ & BUD & _) & _).
    assert (X8 : sec_map_size n / 8 <= (n + MBLK) / 8) by (apply Z.div_le_mono; (lazymatch goal with |- ?G => let G' := eval unfold MBLK in G in change_no_check G' end); lia).
    unfold ROOMSLACK, MBLK, PG in *. lia.   (* [comment removed for export] *)
  Qed.

  Hypothesis BOK : boot_ok bt.
  Hypothesis BTOT : boot_totals bt.

  (* [comment removed for export] *)
  Theorem sec_grant_ex : forall st Lc FF M0 mdl mdlm n, WF bt st Lc FF -> Rep bt st Lc FF M0 mdl -> same_but_materialized mdl mdlm -> MInv (a_aa st) mdlm ->
    a_kact st <= KCAP -> 64513 <= n <= GBUDGET -> eager_used mdl + sec_map_size n + A_bytes (a_aa st) <= vm_limit (m_vmmaps mdl) ->
    exists a : word, grant_ok (Z_to_bv 64 0) mdlm a (sec_map_size n) = true.
  Proof using BTOT BOK.
    intros st Lc FF M0 mdl mdlm n W RP SBM MI KC HN BUD.
    destruct (sbm_vmmaps _ _ SBM) as [EV EL].
    pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (AW & _) & _).
    pose proof (AsKSys6.AsanNodesMmLib.mat_pages_le_A_bytes (a_aa st) mdlm MI AW) as MP.
    pose proof (eager_used_ext mdlm mdl EV EL) as EE.
    apply (grant_exists bt st Lc FF (2 ^ 20) (2 ^ 28) M0 mdl W ltac:(lia) (qroom_WF bt st Lc FF W) RP KC BOK BTOT (Z_to_bv 64 0) mdlm (sec_map_size n) EV).
    - exact (sec_map_size_NZEX n HN).
    - rewrite vm_backing_used_split, EE, EV. lia.
  Qed.
End SecK.

(* [comment removed for export] *)
Lemma HID_off_segments_l : forall {RC : run_ceil} bt st st' mdl mdl', bt_ia bt = both_addrs -> rep_ledger bt st mdl -> m_vm_lazy mdl' = m_vm_lazy mdl ->
  H_off_segments BSEGS (HID st' mdl').
Proof.
  intros RC bt st st' mdl mdl' BI RL EL a Ha.
  apply HID_lazy in Ha. pose proof (u64_range a) as Hr.
  assert (L : lzb mdl (U a) = true) by (unfold lzb in Ha |- *; rewrite EL in Ha; exact Ha).
  destruct (lazy_zone bt st mdl (U a) RL ltac:(lia) L) as [Z1 Z2].
  rewrite BI in Z2. cbn [ia_img_lo ia_img_hi both_addrs] in Z2.
  destruct (find_segment BSEGS (U a) 1) eqn:E; [|reflexivity]. exfalso. apply Z2. apply asanF_segs_hull. rewrite E. discriminate.
Qed.
End BoAllocMSecK.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk.ShapeAlg OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.GlzConst.RunCeil OSSVerify.Proofs.glaze.binary_reflection.lib.MhK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsK OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3.AsRtK OSSVerify.Proofs.glaze.binary_reflection.lib.Common.BackingAlgebra.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsCells OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinv3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3.AsAinvGeom3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFrame3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsAinvBootF3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvZone3b.AsAinvFacts3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOps3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvOpsPf3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3b OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvOpsPf3c OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsS3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsPf3d.AsAinvFreeS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvFree3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23.AsAinvOpsQ3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvOpsQ23 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFFam.AsAinvXTrk3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvEntry3.AsAinvHole3.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKSL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKSL.BoAllocFRcGL OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFRcKS.BoAllocFRcGS OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFPutB.BoAllocFTail OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMSbM4.BoAllocM4s OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM8Lc.BoAllocMHyp OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMTopP2.BoAllocMTopA OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocM9c.BoAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtIMemmove.AsDepotSum2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsDepotBud OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotBud2 OSSVerify.Proofs.glaze.binary_reflection.lib.BoDepotTop3.BoDepotHyp9 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocMRunS2.BoAllocMSumS OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMSbKit BoAllocMSecK BoAllocMSecDefs OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys6.AsKSys7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys7b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys9b OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10 OSSVerify.Proofs.glaze.binary_reflection.lib.AsKSys10.AsKSys11.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require SymExec.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= am_lia.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition sec_footA (S T mb msz P8 len nres : Z) (grow : bool) (z : Z) : Prop :=
  (S - 3584 <= z < S) \/ (mb <= z < mb + msz) \/ (SB + mb / 8 <= z < SB + (mb + msz) / 8)
  \/ (0x10abc8 <= z < 0x10ae28) \/ (P8 + 8 * len <= z < P8 + 8 * len + 8)
  \/ (grow = true /\ P8 + 8 * nres <= z < P8 + 8 * nres + 2 ^ 17) \/ (T + 2872 <= z < T + 2888).

(* [comment removed for export] *)
Definition sec_ideal (mp n : Z) (MD : mem) : mem :=
  let p := mp + sec_user_off n in
  wbytes (wbytes (wbytes (wbytes (wbytes MD
    (Z_to_bv 64 (SB + (mp + PG) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat (p / 8 - (mp + PG) / 8))))
    (Z_to_bv 64 (SB + (p + n + 7) / 8)) (repeat (Z_to_bv 8 250) (Z.to_nat ((mp + sec_map_size n) / 8 - (p + n + 7) / 8))))
    (Z_to_bv 64 (mp + PG)) (LE8 (Z_to_bv 64 MAGIC)))
    (Z_to_bv 64 (mp + PG + 8)) (LE8 (Z_to_bv 64 (p - 16))))
    (Z_to_bv 64 (p - 16)) [Z_to_bv 8 2].

Lemma or_decT : forall A B : Prop, {A} + {~ A} -> {B} + {~ B} -> {A \/ B} + {~ (A \/ B)}.
Proof. intros A B [a|na] [b|nb]; [left; left; exact a | left; left; exact a | left; right; exact b | right; intros [x|x]; [exact (na x) | exact (nb x)]]. Qed.
Lemma ivl_decT : forall lo hi a : Z, {lo <= a < hi} + {~ (lo <= a < hi)}.
Proof. intros lo hi a. destruct (Z_le_dec lo a) as [L|L]; destruct (Z_lt_dec a hi) as [H|H]; [left; split; assumption | right; intros [? ?]; contradiction ..]. Qed.
Lemma sec_hx_dec : forall mp n, Wdec (sec_hx mp n).
Proof. intros mp n a. (lazymatch goal with |- ?G => let G' := eval unfold sec_hx in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). apply or_decT; [apply Z.eq_dec | apply or_decT; [apply ivl_decT | apply or_decT; apply ivl_decT]]. Qed.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Lemma sec_geo : forall mp n, 64512 < n -> n <= 2 ^ 34 -> 0 <= mp -> mp mod 4096 = 0 -> mp + sec_map_size n <= 2 ^ 47 ->
  let p := mp + sec_user_off n in
  sec_user_off n = 6144 /\ n + 8192 <= sec_map_size n <= n + 16384 /\ sec_map_size n mod 4096 = 0
  /\ (mp + PG) / 8 = mp / 8 + 512 /\ p / 8 = mp / 8 + 768 /\ mp / 8 + 768 + n / 8 <= (p + n + 7) / 8 <= (mp + sec_map_size n) / 8
  /\ (mp + sec_map_size n) / 8 = mp / 8 + sec_map_size n / 8 /\ 0 <= mp / 8 /\ (mp + sec_map_size n) / 8 <= 2 ^ 44
  /\ (mp + sec_map_size n + 7) / 8 = (mp + sec_map_size n) / 8.
Proof.
  intros mp n Hn Hn2 Hmp Hal Hhi. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end).
  assert (Erz : rz n = 2048) by (apply rz_sec; lia). pose proof (sec_needed_bnd n Hn) as Hsnb.
  assert (E1 : sec_user_off n = 6144) by ((lazymatch goal with |- ?G => let G' := eval unfold sec_user_off, PG in G in change_no_check G' end); rewrite Erz; reflexivity).
  assert (E2 : sec_needed n + 4096 <= sec_map_size n <= sec_needed n + 8191 /\ sec_map_size n mod 4096 = 0) by ((lazymatch goal with |- ?G => let G' := eval unfold sec_map_size, RoundUp, PG in G in change_no_check G' end); lia).
  rewrite E1. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). generalize dependent (sec_map_size n). intros z. generalize dependent (sec_needed n). intros s. intros.
  repeat split; lia.
Qed.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
Lemma sec_ideal_facts : forall mp n (MD : mem), 64512 < n -> n <= 2 ^ 34 -> AIMGHI <= mp -> mp mod 4096 = 0 -> mp + sec_map_size n <= 2 ^ 47 ->
  (mp + sec_map_size n <= AS_LO \/ AS_HEAPLO <= mp) ->
  let p := mp + sec_user_off n in
  let M0 := sec_ideal mp n MD in
  msum (sec_hx mp n) MD M0
  /\ rdn BSEGS M0 (Z_to_bv 64 (p - 16)) 1 = Some [Z_to_bv 8 2]
  /\ rdn BSEGS M0 (Z_to_bv 64 (mp + PG)) 8 = Some (LE8 (Z_to_bv 64 MAGIC))
  /\ rdn BSEGS M0 (Z_to_bv 64 (mp + PG + 8)) 8 = Some (LE8 (Z_to_bv 64 (p - 16)))
  /\ (forall x : word, (SB + (mp + PG) / 8 <= U x < SB + p / 8) \/ (SB + (p + n + 7) / 8 <= U x < SB + (mp + sec_map_size n) / 8) ->
        M0 x = Some (Z_to_bv 8 250)).
Proof.
  intros mp n MD Hn Hn2 Hmp Hal Hhi Hband. (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). unfold AS_LO, AS_HEAPLO in Hband.
  destruct (sec_geo mp n Hn Hn2 ltac:(lia) Hal Hhi) as (EOFF & GMSZ & GMSZ4 & GQ1 & GQ2 & GQ3 & GQ4 & GQ5 & GQ6 & GQ7).
  (lazymatch goal with |- ?G => let G' := eval unfold sec_ideal, sec_hx in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). rewrite EOFF in *. unfold PG in *. rewrite GQ1, GQ2 in *. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end).
  set (q := mp / 8) in *. set (e := (mp + sec_map_size n) / 8) in *. set (rr := (mp + 6144 + n + 7) / 8) in *.
  assert (QN : 0 <= n / 8) by (apply Z.div_pos; lia).
  replace (q + 768 - (q + 512)) with 256 by lia.
  assert (L1 : Z.of_nat (length (repeat (Z_to_bv 8 250) (Z.to_nat 256))) = 256) by (rewrite length_repeat_Z by lia; reflexivity).
  assert (L2 : Z.of_nat (length (repeat (Z_to_bv 8 250) (Z.to_nat (e - rr)))) = e - rr) by (rewrite length_repeat_Z by lia; reflexivity).
  split; [| split; [| split; [| split]]].
  - apply msum_wbytes_in; [| (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); rewrite u_Z2bv by lia; intros z Hz; left; lia].
    apply msum_wbytes_in; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros z Hz; right; left; lia].
    apply msum_wbytes_in; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros z Hz; right; left; lia].
    apply msum_wbytes_in; [| rewrite L2, u_Z2bv by lia; lia | rewrite L2, u_Z2bv by lia; intros z Hz; right; right; right; lia].
    apply msum_wbytes_in; [| rewrite L1, u_Z2bv by lia; lia | rewrite L1, u_Z2bv by lia; intros z Hz; right; right; left; lia].
    apply msum_refl.
  - apply (rdn_wbytes_hit BSEGS [Z_to_bv 8 2]). rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  - rewrite rdn_wbytes_out; [| (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
    rewrite rdn_wbytes_out; [| rewrite length_N_to_le_bytes, !u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  - rewrite rdn_wbytes_out; [| (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite !u_Z2bv by lia; lia ] | first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
    apply rdn_wbytes_hitw. rewrite u_Z2bv by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
  - intros x Hx. pose proof (u64_range x) as Hxr.
    rewrite wb_out; [| (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat] in G in change_no_check G' end); first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
    rewrite wb_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    rewrite wb_out; [| rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
    destruct Hx as [Hx | Hx].
    + rewrite wb_out; [| rewrite L2, u_Z2bv by lia; lia | rewrite L2, u_Z2bv by lia; lia].
      rewrite wbytes_inside; [| rewrite L1, u_Z2bv by lia; lia | rewrite L1, u_Z2bv by lia; lia].
      rewrite nth_repeat_inS; [reflexivity | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
    + rewrite wbytes_inside; [| rewrite L2, u_Z2bv by lia; lia | rewrite L2, u_Z2bv by lia; lia].
      rewrite nth_repeat_inS; [reflexivity | first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]].
Qed.

Lemma le4_mod32 : forall n, 0 <= n < 2 ^ 64 -> word_to_le_bytes 4 (Z_to_bv 64 (n mod 2 ^ 32)) = word_to_le_bytes 4 (Z_to_bv 64 n).
Proof.
  intros n Hn. pose proof (Z.mod_pos_bound n (2 ^ 32) ltac:(lia)) as Hm. (lazymatch goal with |- ?G => let G' := eval unfold word_to_le_bytes in G in change_no_check G' end). rewrite !u_Z2bv by lia.
  exact (SymExec.Z_to_le_bytes_mod 4 n).
Qed.


(* [comment removed for export] *)
Lemma store_ok1_defD : forall (m : mem) (a : word), m a <> None -> store_ok BSEGS m a 1%nat = true.
Proof.
  intros m a D. apply store_ok_of_all; [pose proof (u64_range a); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia|].
  intros x Hx. assert (x = a) by (apply bv_eq; cbn in Hx; lia). subst x. (lazymatch goal with |- ?G => let G' := eval unfold wview in G in change_no_check G' end). destruct (m a); [discriminate | exact (False_ind _ (D eq_refl))].
Qed.

Section WithCeil.
Context {RC : run_ceil}.

(* [comment removed for export] *)
Lemma fresh_vs_node : forall bt st Lc FF, WF bt st Lc FF -> forall lo hi,
  (forall l h, In (l, h) (all_ranges bt st) -> hi <= l \/ h <= lo) ->
  forall id z, 1 <= id <= dp_nids (a_dep st) -> (lo <= z < hi \/ in_band z) -> ~ foot_node bt (a_dep st) id z.
Proof using.
  intros bt st Lc FF W lo hi AP id z Hid Hz HN. unfold foot_node in HN.
  destruct (node_addr_range bt st Lc FF W id Hid) as (HIn & N1 & N2 & N3). pose proof (node_addr_block bt st id Hid) as Hbk.
  set (bb := nth (Z.to_nat (id / 2 ^ 16)) (node_blocks bt (a_dep st)) 0) in *. clearbody bb.
  assert (INR : In (bb, bb + 2 ^ 20) (all_ranges bt st)).
  { destruct HIn as [Eb | Hnb].
    - pose proof (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & INN & _). rewrite <- Eb. exact (all_ranges_fixed bt st _ INN).
    - exact (all_ranges_dyn bt st _ (node_dyn st bb Hnb)). }
  destruct Hz as [Hz | Hz].
  - destruct (AP _ _ INR) as [D | D]; lia.
  - pose proof W as (_ & _ & _ & _ & _ & _ & _ & _ & (RNG & _) & _).
    destruct (RNG _ _ INR) as ((D1 & D2 & D3 & D4 & D5) & _). unfold in_band in Hz. lia.
Qed.

Section TOPSD.
  Variable bt : as_boot.
  Variable FXOK : FPState -> Prop.
  Variable KD : Z.
  Hypothesis BT_segs : bt_segs bt = BSEGS.
  Hypothesis BT_ia : bt_ia bt = both_addrs.
  Hypothesis G_KD : 0 <= KD <= 1312.
  Hypothesis HYP_DEPOT9 : BoDepotTop3.BoDepotHyp9.HYP_DEPOT9_stmt bt FXOK KD.

  #[local] Abbreviation T := (bt_thread bt).
  #[local] Abbreviation P8 := (bt_ptrarr bt).

  Theorem sec_at_depot :
    forall fx (R : bvmap 5 word) (M : mem) (mdl : Model) (Lc FF : list (Z * Z)) (B C K ret sp n : Z) (st : ast) (h : option Z) (Qok : config -> Prop)
           (r : bvmap 5 word) (MD : mem) (mdlD : Model) (mb : Z) (grow : bool) (x18 x19 : word) (sz : Z),
      let S := getr R 2 in
      let msz := sec_map_size n in
      let p := mb + sec_user_off n in
      let len := Z.of_nat (length (a_sec st)) in
      let nres' := (if grow then a_nres st + 2 ^ 14 else a_nres st) in
      let A2 := a_aa st ++ sec_naa mb n in
      FXOK fx ->
      WF bt st Lc FF -> Rep bt st Lc FF M mdl -> bounds st Lc B C K -> holes_le h st ->
      call_pre BSEGS both_addrs R M ret sp MSTK_A -> 64512 < n <= NMAX ->
      B + (n + MBLK) <= GBUDGET -> C + 1 <= LMAX -> K + kcost_malloc n <= KCAP ->
      (* [comment removed for export] *)
      mb mod PG = 0 -> dyn_ok (bt_ia bt) mb (mb + msz) ->
      (forall lo hi, In (lo, hi) (all_ranges bt st) -> mb + msz <= lo \/ hi <= mb) ->
      (forall b0 n0, In (b0, n0) (bt_maps0 bt) -> mb + msz <= U b0 \/ U b0 + U n0 <= mb) ->
      (grow = true <-> len = a_nres st) ->
      (* [comment removed for export] *)
      m_halted mdlD = None -> BackingAlgebra.model_ivs_wf mdlD -> MInv A2 mdlD ->
      vm_maps (m_vmmaps mdlD) = (Z_to_bv 64 mb, Z_to_bv 64 msz) :: vm_maps (m_vmmaps mdl) ->
      (forall a, in_ivz (vm_noaccess (m_vmmaps mdlD)) a <->
                 in_ivz (vm_noaccess (m_vmmaps mdl)) a /\ ~ (grow = true /\ P8 + 8 * a_nres st <= a < P8 + 8 * a_nres st + 2 ^ 17)) ->
      Forall (fun e : word * word => 0 < bv_unsigned (snd e)) (vm_noaccess (m_vmmaps mdlD)) ->
      (forall a, pg_in_ivz (m_vm_lazy mdlD) a <->
                 pg_in_ivz (m_vm_lazy mdl) a /\ ~ (grow = true /\ P8 + 8 * a_nres st <= a < P8 + 8 * a_nres st + 2 ^ 17)) ->
      Forall (fun iv : word * word => bv_unsigned (fst iv) mod PG = 0 /\ bv_unsigned (snd iv) mod PG = 0
                                     /\ 0 < bv_unsigned (fst iv) /\ bv_unsigned (fst iv) + bv_unsigned (snd iv) <= CEIL
                                     /\ (bv_unsigned (fst iv) + bv_unsigned (snd iv) <= ia_img_lo (bt_ia bt) \/ ia_img_hi (bt_ia bt) <= bv_unsigned (fst iv)))
             (m_vm_lazy mdlD) ->
      vm_reserved (m_vmmaps mdlD) = vm_reserved (m_vmmaps mdl) -> vm_brk (m_vmmaps mdlD) = vm_brk (m_vmmaps mdl) ->
      vm_start_brk (m_vmmaps mdlD) = vm_start_brk (m_vmmaps mdl) -> vm_mmap_base (m_vmmaps mdlD) = vm_mmap_base (m_vmmaps mdl) ->
      vm_init_sp (m_vmmaps mdlD) = vm_init_sp (m_vmmaps mdl) -> vm_limit (m_vmmaps mdlD) = vm_limit (m_vmmaps mdl) ->
      eager_used mdlD <= eager_used mdl + msz + (if grow then 2 ^ 17 else 0) ->
      same_except_vm mdl mdlD ->
      (forall a, 0 <= a < 2 ^ 64 -> ~ (grow = true /\ P8 + 8 * a_nres st <= a < P8 + 8 * a_nres st + 2 ^ 17) -> lzb mdlD a = lzb mdl a) ->
      (* [comment removed for export] *)
      mem_grows M MD ->
      (forall x : word, MD x <> M x -> sec_footA (U S) T mb msz P8 len (a_nres st) grow (U x)) ->
      rdn BSEGS MD (Z_to_bv 64 mb) 8 = Some (LE8 (Z_to_bv 64 mb)) ->
      rdn BSEGS MD (Z_to_bv 64 (mb + 8)) 8 = Some (LE8 (Z_to_bv 64 msz)) ->
      rdn BSEGS MD (Z_to_bv 64 (mb + 16)) 8 = Some (LE8 (Z_to_bv 64 (sec_needed n))) ->
      rdn BSEGS MD (Z_to_bv 64 (mb + 24)) 8 = Some (LE8 (Z_to_bv 64 len)) ->
      rdn BSEGS MD (Z_to_bv 64 (P8 + 8 * len)) 8 = Some (LE8 (Z_to_bv 64 mb)) ->
      rdn BSEGS MD (Z_to_bv 64 0x10abc8) 8 = Some (LE8 (Z_to_bv 64 nres')) ->
      rdn BSEGS MD (Z_to_bv 64 0x10abd0) 8 = Some (LE8 (Z_to_bv 64 (len + 1))) ->
      rdn BSEGS MD (Z_to_bv 64 0x10ae00) 1 = Some [Z_to_bv 8 0] ->
      (forall x : word, SB + mb / 8 <= U x < SB + mb / 8 + 512 -> MD x = Some (Z_to_bv 8 250)) ->
      MD (Z_to_bv 64 (p - 15)) = Some (Z_to_bv 8 (U (hb1w (Z_to_bv 64 0)))) ->
      rdn BSEGS MD (Z_to_bv 64 (p - 14)) 2 = Some (LE2 (n / 2 ^ 32)) ->
      rdn BSEGS MD (Z_to_bv 64 (p - 12)) 4 = Some (LE4 n) ->
      (forall x : word, mb <= U x < mb + msz -> MD x <> None) ->
      (forall x : word, p - 4 <= U x < p -> MD x = Some (Z_to_bv 8 0)) ->
      (grow = true -> forall x : word, P8 + 8 * a_nres st <= U x < P8 + 8 * a_nres st + 2 ^ 17 -> MD x <> None) ->
      (* [comment removed for export] *)
      (forall (k0 : Z) (v : word),
          In (k0, v) (ma_slotsA S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) ->
          rdn BSEGS MD (at_ S k0) 8 = Some (LE8 v)) ->
      (forall (k0 : Z) (v : word),
          In (k0, v) [(-8, getr R 1); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
          rdn BSEGS MD (at_ S k0) 8 = Some (LE8 v)) ->
      (* [comment removed for export] *)
      getr r 1 = Z_to_bv 64 0x4c940 -> getr r 2 = at_ S (-2272) -> getr r 10 = at_ S (-2112) -> getr r 11 = Z_to_bv 64 sz -> 1 <= sz <= 8 ->
      getr r 4 = getr R 4 -> getr r 3 = getr R 3 ->
      getr r 8 = Z_to_bv 64 0 -> getr r 9 = Z_to_bv 64 n -> getr r 18 = Z_to_bv 64 (mb + PG)
      -> getr r 19 = Z_to_bv 64 (sec_needed n) -> getr r 20 = Z_to_bv 64 p -> getr r 21 = Z_to_bv 64 (p - 16)
      -> getr r 22 = Z_to_bv 64 0x10ab58 -> getr r 23 = at_ S (-2128) -> getr r 24 = Z_to_bv 64 0
      -> getr r 25 = Z_to_bv 64 (p + n) -> getr r 26 = Z_to_bv 64 T -> getr r 27 = Z_to_bv 64 1 ->
      (forall c'', runS_post bt FXOK st Lc FF R M mdl n c'' -> katD BSEGS c'' Qok) ->
      katD BSEGS (mkCfg (@mkst fx r (Z_to_bv 64 0x8f4f0) MD (seg_rom BSEGS)) mdlD) Qok.
  Proof using HYP_DEPOT9 G_KD BT_ia BT_segs KD.
    intros fx R M mdl Lc FF B C K ret sp n st h Qok r MD mdlD mb grow x18 x19 sz S msz p len nres' A2
           HFX W RP BD HLE CP Hn HB HC HK AL DY AP APM0 HGROW HHD MWD MID
           LVM LNA LNP LLZ LLF LRS LBK LSB LMB LIS LLIM LEG SEV LZB
           GRD FOOTD C_mb C_msz C_need C_idx C_ptr C_nres C_nch C_lk C_fa C_h15 C_h14 C_h12 C_def C_z4 C_slice
           F_slots F_islots X1 X2 X10 X11 SZ8 X4 X3 X8 X9 X18 X19 X20 X21 X22 X23 X24 X25 X26 X27 CONT.
    pose proof ceil_rng as CR. pose proof ceil_pg as CPG.
    destruct CP as (CP1 & CPr & CPe & CP2 & CP16 & CPlo & CPhi & CP4 & CPstk). fold S in CP2.
    pose proof BD as ((BP0 & BP1) & BC1 & (BK0 & BK1)).
    assert (Hn1 : 64512 < n) by lia.
    assert (Hn34 : 64513 <= n <= 2 ^ 34) by (unfold GBUDGET, MBLK in HB; lia).
    destruct (sec_msz_bnd n Hn1) as [MZ1 MZ2]. fold msz in MZ1, MZ2.
    pose proof DY as (Y1 & Y2 & Y3 & Y4 & Y5). rewrite BT_ia in Y4. cbn [ia_img_lo ia_img_hi both_addrs] in Y4.
    assert (GA : AIMGHI <= mb) by lia.
    unfold PG in AL.
    destruct (sec_geo mb n Hn1 ltac:(lia) ltac:(lia) AL ltac:(fold msz; lia)) as (EOFF & GMSZ & GMSZ4 & GQ1 & GQ2 & GQ3 & GQ4 & GQ5 & GQ6 & GQ7).
    fold msz p in GMSZ, GMSZ4, GQ2, GQ3, GQ4, GQ6, GQ7.
    assert (Ep : p = mb + 6144) by ((lazymatch goal with |- ?G => let G' := eval unfold p in G in change_no_check G' end); rewrite EOFF; reflexivity).
    pose proof (u64_range S) as HSr.
    unfold PTRHI in CPlo, CPhi. unfold MSTK_A in CPlo, CPstk.
    assert (CEILS : CEIL + 3584 <= U S) by (rewrite CP2; lia).
    hidehypW Y4. hidehypW Y5.
    (* [comment removed for export] *)
    set (naa := sec_naa mb n) in *. set (shs := sec_hull mb n).
    pose proof (sec_shs_bnd mb n ltac:(clear - GA; lia) Hn1) as SH0. fold shs in SH0.
    set (st1 := op_meter st EVT [] 0).
    assert (W1 : WF bt st1 Lc FF) by (apply WF_meter; [exact W | (lazymatch goal with |- ?G => let G' := eval unfold EVT in G in change_no_check G' end); clear; lia | reflexivity]).
    destruct (rooms_meter bt st Lc FF EVT [] (2 ^ 20) (2 ^ 28) W ltac:(clear; lia)) as (_ & SR1 & _). fold st1 in SR1.
    pose proof RP as (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11 & R12 & R13 & R14 & R15 & R16 & R17 & R18).
    destruct R14 as (Bw1 & Bw2 & Bw3 & Bw4 & Bw5).
    rewrite BT_segs in *.
    pose proof (sec_pre_budget bt st Lc FF M mdl B C K n mb RP W BD Hn1 HB HK ltac:(clear - GA; lia)) as BUDG. fold msz in BUDG. fold shs in BUDG.
    assert (AW2 : A_wf A2) by (apply sec_naa_wf; [exact Bw1 | lia | exact Hn1]).
    assert (AB2 : A_bytes A2 = A_bytes (a_aa st) + shs) by ((lazymatch goal with |- ?G => let G' := eval unfold A2, naa, shs in G in change_no_check G' end); rewrite A_bytes_app, sec_naa_bytes; reflexivity).
    assert (RP1 : Rep bt st1 Lc FF M mdl).
    { apply (OPS_REP_meter_pf bt st Lc FF M mdl mdl EVT [] 0 RP eq_refl).
      - intros a; am_tauto.
      - pose proof RP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (_ & _ & _ & FA & _) & _). exact FA.
      - rewrite app_nil_r. exact Bw1.
      - rewrite app_nil_r. exact Bw2.
      - clear; lia.
      - (lazymatch goal with |- ?G => let G' := eval cbn [A_bytes] in G in change_no_check G' end). clear; lia. }
    assert (KC : a_kact st <= KCAP) by (unfold kcost_malloc, EVT in HK; lia).
    assert (ROOM : grow = true -> a_nres st + 2 ^ 14 <= 2 ^ 20).
    { intros G. apply HGROW in G.
      pose proof (sec_len_le bt st Lc FF (2 ^ 20) (2 ^ 28) W ltac:(lia)) as SL.
      pose proof W as (_ & _ & _ & (NR1 & NR2 & NR3 & _) & _).
      assert (Q : QSECCNT = 4193) by reflexivity. fold len in SL. unfold LMAX in SL. rewrite Q in SL.
      clear - G SL NR2 NR3. Z.div_mod_to_equations. lia. }
    set (st2 := op_sec_alloc st1 mb n grow).
    assert (W2 : WF bt st2 ((p, n) :: Lc) FF).
    { apply (OPS_WF_sec_alloc_pf bt st1 Lc FF mb n grow W1); [lia | (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact AL | exact DY | exact AP | exact HGROW | exact ROOM | lia | lia | exact APM0 | exact SR1]. }
    (* [comment removed for export] *)
    pose proof (sec_len_le bt st Lc FF (2 ^ 20) (2 ^ 28) W ltac:(lia)) as SLEN. fold len in SLEN. unfold LMAX in SLEN.
    replace QSECCNT with 4193 in SLEN by reflexivity.
    assert (LEN0 : 0 <= len) by ((lazymatch goal with |- ?G => let G' := eval unfold len in G in change_no_check G' end); lia).
    pose proof W as (_ & _ & _ & (NR1 & NR2 & NR3 & _) & _). fold len in NR1.
    pose proof (thread_dyn bt st Lc FF W) as (GT0 & GTC & GTI & GTB & TPG & _).
    rewrite BT_ia in GTI. cbn [ia_img_lo ia_img_hi both_addrs] in GTI. unfold PG in GTC, GTI, GTB, TPG.
    destruct (fixed_members bt st Lc FF W) as (IN6 & IN8 & _ & INT & _ & _ & INC).
    pose proof (AP _ _ (all_ranges_fixed bt st _ INT)) as APT. pose proof (AP _ _ (all_ranges_fixed bt st _ IN8)) as AP8. unfold PG in APT.
    assert (IMGLO' : ia_img_lo (bt_ia bt) <= 65536) by (rewrite BT_ia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia).
    pose proof (ptrarr_geom bt st Lc FF W IMGLO') as (PA1 & PA2 & PA3 & PA4 & PA5 & PA6 & PA7 & PA8).
    rewrite BT_ia in PA1. cbn [ia_img_hi both_addrs] in PA1. unfold PG in PA6.
    hidehypW GTI. hidehypW GTB. hidehypW APT. hidehypW AP8. hidehypW PA4. hidehypW PA5. hidehypW PA6. hidehypW PA7.
    unfold AS_LO, AS_HEAPLO in *. unfold SB in *.
    set (q := mb / 8) in *. set (e := (mb + msz) / 8) in *.
    assert (QN : 0 <= n / 8) by (apply Z.div_pos; lia).
    (* [comment removed for export] *)
    assert (HXG : forall z, sec_hx mb n z -> (mb + 4096 <= z < mb + 6129) \/ (2147450880 + q + 512 <= z < 2147450880 + e)).
    { intros z Hz. unfold sec_hx in Hz. cbv zeta in Hz. fold p msz in Hz. rewrite GQ1, GQ2 in Hz. fold e in Hz. unfold PG, SB in Hz.
      clear - Hz Ep GQ3 QN. lia. }
    assert (NHX : forall z, (z < mb + 4096 \/ mb + 6129 <= z) -> (z < 2147450880 + q + 512 \/ 2147450880 + e <= z) -> ~ sec_hx mb n z).
    { intros z H1 H2 Hz. destruct (HXG z Hz) as [D|D]; clear - D H1 H2; lia. }
    (* [comment removed for export] *)
    set (M0 := sec_ideal mb n MD).
    pose proof (sec_ideal_facts mb n MD Hn1 ltac:(lia) GA AL ltac:(fold msz; lia) ltac:(fold msz; unfold hideW in Y5; exact Y5)) as IF.
    cbv zeta in IF. fold M0 p msz in IF. destruct IF as (I_sum & I_st & I_mag & I_lch & I_fa).
    rewrite GQ1, GQ2 in I_fa. fold e in I_fa. unfold SB in I_fa. unfold PG in I_mag, I_lch.
    pose proof I_sum as [OFF0 GR0].
    assert (RD0 : forall (z : Z) (k : nat) bs, 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 -> (forall i, z <= i < z + Z.of_nat k -> ~ sec_hx mb n i) ->
              rdn BSEGS MD (Z_to_bv 64 z) k = Some bs -> rdn BSEGS M0 (Z_to_bv 64 z) k = Some bs).
    { intros z k bs Hz0 Hz1 Hoff Hr. apply (msum_rdn_eq BSEGS (sec_hx mb n) MD M0 _ k bs I_sum); [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ] | rewrite u_Z2bv by lia; exact Hoff | exact Hr]. }
    assert (DEFD : forall x : word, MD x <> M x -> MD x <> None).
    { intros x NE E. apply NE. rewrite E. destruct (M x) eqn:E2; [| reflexivity]. exfalso. assert (X : M x <> None) by (rewrite E2; discriminate). apply GRD in X. exact (X E). }
    assert (WRdef : forall lo hi, (forall i, lo <= i < hi -> M0 (Z_to_bv 64 i) <> None) -> writableZ BSEGS M0 lo hi).
    { intros lo hi D i Hi. split; [exact (D i Hi) | exact (store_ok1_defD _ _ (D i Hi))]. }
    (* [comment removed for export] *)
    assert (KEEPM : forall (z : Z) (k : nat) bs, 0 <= z < 2 ^ 64 -> z + Z.of_nat k <= 2 ^ 64 ->
              (forall i, z <= i < z + Z.of_nat k -> ~ sec_footA (U S) T mb msz P8 len (a_nres st) grow i) ->
              rdn BSEGS M (Z_to_bv 64 z) k = Some bs -> rdn BSEGS MD (Z_to_bv 64 z) k = Some bs).
    { intros z k bs Hz0 Hz1 Hoff Hr. rewrite <- Hr. apply rdn_ext; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia.
      destruct (decide (MD x = M x)) as [E|NE]; [exact E|]. exfalso. exact (Hoff _ Hx (FOOTD x NE)). }
    destruct R2 as (Inres & Inch & Ilock & _ & _ & _ & _ & Ichunks & Iptrw).
    destruct R3 as (Tctx & Ttop & Tbot & Tsw & Tfs & Tunw & TQ & TPC & TW & Tback & Ttid & Ttls1 & Ttls2).
    rewrite BT_segs in Tunw, Iptrw.
    assert (SLICE : grow = true -> a_nres st = 0) by (intros G; apply HGROW in G; clear - G SLEN NR2 NR3; Z.div_mod_to_equations; lia).
    assert (RP2 : Rep bt st2 ((p, n) :: Lc) FF M0 mdlD).
    { apply (OPS_REP_sec_alloc_pf bt st1 Lc FF M M0 mdl mdlD mb n grow W1 RP1 ltac:(lia) ltac:((lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact AL) DY AP HGROW ROOM); rewrite ?BT_segs;
        change (Z.of_nat (length (a_sec st1))) with len; change (a_nres st1) with (a_nres st); change (a_aa st1) with (a_aa st ++ []); fold p; fold msz.
      - (* [comment removed for export] *)
        intros a NE. pose proof (u64_range a) as Har.
        assert (FT : forall z, sec_footA (U S) T mb msz P8 len (a_nres st) grow z -> foot_sec_alloc bt st1 mb n grow z).
        { intros z [F|[F|[F|[F|[F|[F|F]]]]]]; (lazymatch goal with |- ?G => let G' := eval unfold foot_sec_alloc in G in change_no_check G' end).
          - do 6 right. clear - F CEILS. lia.
          - left. exact F.
          - right; left. (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end). fold msz. rewrite GQ7. fold q e. exact F.
          - right; right; left. (lazymatch goal with |- ?G => let G' := eval unfold IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). clear - F. lia.
          - do 3 right; left. exact F.
          - do 4 right; left. exact F.
          - do 5 right; left. (lazymatch goal with |- ?G => let G' := eval unfold T_UNW in G in change_no_check G' end). clear - F. lia. }
        destruct (decide (M0 a = MD a)) as [E|NE0].
        + rewrite E in NE |- *. split; [exact (FT _ (FOOTD a NE)) | exact (DEFD a NE)].
        + destruct (msum_changed (sec_hx mb n) MD M0 (sec_hx_dec mb n) I_sum a NE0) as [HX D]. split; [| exact D].
          destruct (HXG _ HX) as [G|G]; [left; fold msz; clear - G GMSZ Hn1; lia | right; left; (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, sh_hi, SB in G in change_no_check G' end); fold msz; rewrite GQ7; fold q e; clear - G; lia].
      - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
        apply (RD0 _ 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply NHX; clear - Hi GA GQ5; lia | exact C_nres].
      - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end).
        apply (RD0 _ 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply NHX; clear - Hi GA GQ5; lia | exact C_nch].
      - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN, IB in G in change_no_check G' end). rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_instance both_addrs] in G in change_no_check G' end). rewrite w2b1 by lia.
        apply (RD0 _ 1%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; apply NHX; clear - Hi GA GQ5; lia | exact C_lk].
      - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
        apply (RD0 _ 8%nat); [clear - PA1 PA2 CR LEN0 SLEN; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - PA1 PA2 CR SLEN LEN0; lia | | exact C_ptr].
        intros i Hi. cbn in Hi. unfold hideW in AP8, PA4. apply NHX; clear - Hi AP8 PA4 SLEN LEN0 GQ5 GQ6 GMSZ Hn1; lia.
      - (* [comment removed for export] *) apply WRdef. intros i Hi. apply GR0.
        destruct (Z_lt_le_dec i (P8 + 8 * a_nres st)) as [L|L].
        + apply GRD. exact (proj1 (Iptrw i ltac:(clear - Hi L; lia))).
        + assert (EG : grow = true) by (destruct grow; [reflexivity | exfalso; clear - Hi L; lia]).
          pose proof (ROOM EG) as RM. rewrite EG in Hi. apply (C_slice EG). rewrite u_Z2bv by (clear - Hi PA1 PA2 CR RM L NR3; lia). clear - Hi L. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply (RD0 _ 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Y5 GQ5 GQ6 GMSZ Hn1; lia | exact C_mb].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply (RD0 _ 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Y5 GQ5 GQ6 GMSZ Hn1; lia | exact C_msz].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply (RD0 _ 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Y5 GQ5 GQ6 GMSZ Hn1; lia | exact C_need].
      - (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply (RD0 _ 8%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Y5 GQ5 GQ6 GMSZ Hn1; lia | exact C_idx].
      - (* [comment removed for export] *) apply WRdef. intros i Hi. apply GR0. apply C_def. rewrite u_Z2bv by lia. exact Hi.
      - (* [comment removed for export] *) (lazymatch goal with |- ?G => let G' := eval unfold rep_hdr in G in change_no_check G' end). rewrite BT_segs. split; [| split; [| split; [| split; [| split; [| split]]]]].
        + (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite w2b1 by lia. exact I_st.
        + exists 0x11. split; [left; reflexivity|]. (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). rewrite w2b1 by lia.
          apply (RD0 _ 1%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Ep Y5 GQ5 GQ6 GMSZ Hn1; lia |].
          apply heap_rdn1; [first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]|]. rewrite C_h15. reflexivity.
        + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). apply (RD0 _ 2%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Ep Y5 GQ5 GQ6 GMSZ Hn1; lia | exact C_h14].
        + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end). rewrite (le4_mod32 n ltac:(lia)).
          apply (RD0 _ 4%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Ep Y5 GQ5 GQ6 GMSZ Hn1; lia | exact C_h12].
        + apply WRdef. intros i Hi. apply GR0. apply C_def. rewrite u_Z2bv by lia. clear - Hi Ep GMSZ Hn1. lia.
        + (lazymatch goal with |- ?G => let G' := eval unfold cellZ, cellN in G in change_no_check G' end).
          assert (Z4 : rdn BSEGS MD (Z_to_bv 64 (p - 4)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0))).
          { replace (word_to_le_bytes 4 (Z_to_bv 64 0)) with (repeat (Z_to_bv 8 0) 4) by reflexivity.
            apply rdn_const; [first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite u_Z2bv by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite u_Z2bv in Hx by lia. cbn in Hx. apply C_z4. clear - Hx. lia. }
          apply (RD0 _ 4%nat); [lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | intros i Hi; cbn in Hi; unfold hideW in Y5; apply NHX; clear - Hi Ep Y5 GQ5 GQ6 GMSZ Hn1; lia | exact Z4].
        + intros _. rewrite (rz_sec n Hn1). replace (p - 2048) with (mb + 4096) by (clear - Ep; lia). replace (mb + 4096 + 8) with (mb + 4096 + 8) by reflexivity.
          split; [exact I_mag | exact I_lch].
      - (* [comment removed for export] *)
        intros g Hg NU. unfold user_granule in NU. fold q e in Hg. rewrite GQ2 in NU.
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN, FA in G in change_no_check G' end). rewrite w2b1 by lia. (lazymatch goal with |- ?G => let G' := eval unfold SB in G in change_no_check G' end).
        apply heap_rdn1; [rewrite u_Z2bv by (clear - Hg GQ5 GQ6; lia); clear - Hg GQ5; lia|].
        destruct (Z_lt_le_dec g (q + 512)) as [L|L].
        + rewrite OFF0 by (rewrite u_Z2bv by (clear - Hg GQ5 GQ6; lia); unfold hideW in Y5; apply NHX; clear - Hg L Y5 GQ5 GQ6 GMSZ Hn1; lia).
          apply C_fa. rewrite u_Z2bv by (clear - Hg GQ5 GQ6; lia). clear - Hg L. lia.
        + apply I_fa. rewrite u_Z2bv by (clear - Hg GQ5 GQ6; lia). clear - Hg L NU. lia.
      - (* [comment removed for export] *)
        (lazymatch goal with |- ?G => let G' := eval unfold byteZ, cellN in G in change_no_check G' end). unfold byteZ, cellN in Tunw. unfold T_UNW in *.
        unfold hideW in GTI, GTB, APT, PA6.
        apply (RD0 _ 1%nat); [clear - GT0 GTC CR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GT0 GTC CR; lia | intros i Hi; cbn in Hi; apply NHX; clear - Hi APT GTB GQ5 GQ6 GMSZ Hn1; lia |].
        apply (KEEPM _ 1%nat); [clear - GT0 GTC CR; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - GT0 GTC CR; lia | | exact Tunw].
        intros i Hi. cbn in Hi. intros [F|[F|[F|[F|[F|[F|F]]]]]].
        + clear - F Hi GTC CEILS. lia.
        + clear - F Hi APT. lia.
        + clear - F Hi GTB GQ5 GQ6. fold q e in F. unfold SB in F. lia.
        + clear - F Hi GTI. lia.
        + clear - F Hi PA6 SLEN LEN0. lia.
        + destruct F as [EG F]. pose proof (ROOM EG) as RM. clear - F Hi PA6 RM NR3. lia.
        + clear - F Hi. lia.
      - rewrite LVM. apply Permutation_refl.
      - exact LNA.
      - exact LNP.
      - exact LLZ.
      - exact LLF.
      - exact LRS.
      - exact LBK.
      - exact LSB.
      - exact LMB.
      - exact LIS.
      - exact LLIM.
      - (* [comment removed for export] *) rewrite app_nil_r. exact MID.
      - exact LEG. }
    (* [comment removed for export] *)
    assert (SHM : forall z, 2147450880 + q <= z < 2147450880 + e -> shmaps z).
    { intros z Hz. (lazymatch goal with |- ?G => let G' := eval unfold shmaps, AS_LO, AS_GAPLO, AS_GAPHI, AS_HEAPLO in G in change_no_check G' end). unfold hideW in Y5. destruct Y5 as [Y|Y].
      - left. assert (e <= 268430848) by ((lazymatch goal with |- ?G => let G' := eval unfold e in G in change_no_check G' end); apply Z.div_le_upper_bound; [lia | clear - Y; lia]). clear - Hz H GQ5. lia.
      - right. assert (2199291686912 <= q) by ((lazymatch goal with |- ?G => let G' := eval unfold q in G in change_no_check G' end); apply Z.div_le_lower_bound; [lia | clear - Y; lia]). clear - Hz H GQ6. lia. }
    assert (HXD : forall a : word, sec_hx mb n (U a) -> MD a <> None).
    { intros a HX. destruct (HXG _ HX) as [G|G].
      - apply C_def. clear - G GMSZ Hn1. lia.
      - apply GRD. destruct R18 as (_ & SHD & _). rewrite <- (Z_to_bv_bv_unsigned 64 a). apply SHD. apply SHM. clear - G. lia. }
    assert (KCW : a_kact st2 <= KCAP).
    { (lazymatch goal with |- ?G => let G' := eval cbn [st2 st1 op_sec_alloc set_sec op_meter add_meter a_kact] in G in change_no_check G' end). unfold kcost_malloc in HK. clear - BK1 HK. lia. }
    assert (QK : a_kact st / EVT + 1 <= a_kact st2 / EVT).
    { (lazymatch goal with |- ?G => let G' := eval cbn [st2 st1 op_sec_alloc set_sec op_meter add_meter a_kact] in G in change_no_check G' end). rewrite meter_div by (clear - BK0; lia). clear. lia. }
    pose proof (free_obls_pf bt) as (_ & _ & _ & _ & _ & _ & _ & _ & OBL_store_private).
    unfold OBL_store_private_stmt in OBL_store_private.
    assert (HPRIM : is_primary n = false) by (apply not_primary_big; lia).
    assert (INS2 : In (SCH mb n) (a_sec st2)) by ((lazymatch goal with |- ?G => let G' := eval cbn [st2 st1 op_sec_alloc set_sec op_meter add_meter a_sec] in G in change_no_check G' end); apply in_or_app; right; left; reflexivity).
    assert (PRIVmap : forall z, mb <= z < mb + msz -> rt_priv (bt_ia bt) Lc FF z).
    { intros z Hz. exact (sec_live_private bt st2 ((p, n) :: Lc) FF W2 IMGLO' [] Lc p n (SCH mb n) z eq_refl HPRIM INS2 eq_refl eq_refl Hz). }
    assert (PRIVsh : forall z, 2147450880 + q <= z < 2147450880 + e -> rt_priv (bt_ia bt) Lc FF z).
    { intros z Hz. apply (sec_live_shadow_private bt st2 ((p, n) :: Lc) FF W2 IMGLO' [] Lc p n (SCH mb n) z eq_refl HPRIM INS2 eq_refl eq_refl).
      (lazymatch goal with |- ?G => let G' := eval unfold sh_lo, SB, sc_mapsz in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [sc_map sc_n] in G in change_no_check G' end). fold msz q. rewrite GQ4 in Hz. clear - Hz. lia. }
    assert (PRIVI : forall z, 0x10ab58 <= z < 0x10b9b8 -> in_wins (ia_priv (bt_ia bt)) z).
    { intros z Hz. rewrite BT_ia. exists 0x10ab58, 0x10b9b8. split; [(lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); am_tauto | exact Hz]. }
    assert (PRIVfoot : forall z, sec_footA (U S) T mb msz P8 len (a_nres st) grow z ->
              (U S - 3584 <= z < U S) \/ rt_priv (bt_ia bt) Lc FF z \/ in_wins (ia_priv (bt_ia bt)) z).
    { intros z [F|[F|[F|[F|[F|[F|F]]]]]].
      - left. exact F.
      - right; left. exact (PRIVmap z F).
      - right; left. apply PRIVsh. unfold SB in F. fold q e in F. exact F.
      - right; right. apply PRIVI. clear - F. lia.
      - right; left. apply (ptrarr_private bt st Lc FF W z). clear - F SLEN LEN0. lia.
      - right; left. destruct F as [EG F]. pose proof (ROOM EG) as RM. apply (ptrarr_private bt st Lc FF W z). clear - F RM NR3. lia.
      - right; left. apply (OBL_rt_private_pf bt st Lc FF W z). left. (lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end). clear - F. lia. }
    set (X := sec_hx mb n).
    apply (katD_bind BSEGS _ (depot_post bt FXOK KD X st2 ((p, n) :: Lc) FF MD mdlD r (at_ S (-2272)) (Z_to_bv 64 0x4c940))).
    { apply (HYP_DEPOT9 fx X st2 ((p, n) :: Lc) FF MD mdlD r (at_ S (-2272)) (at_ S (-2112)) (Z_to_bv 64 sz) (Z_to_bv 64 0x4c940) sz HFX HHD MWD W2).
      { exists M0. split; [exact RP2|]. intros a NE.
        assert (NE' : M0 a <> MD a) by (intros E; apply NE; symmetry; exact E).
        destruct (msum_changed (sec_hx mb n) MD M0 (sec_hx_dec mb n) I_sum a NE') as [HX _]. split; [exact HX | exact (HXD a HX)]. }
      { intros a Ha. rewrite BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end). split.
        - destruct (HXG _ Ha) as [G|G]; clear - G GA GQ5; lia.
        - intros id Hid. apply (fresh_vs_node bt st Lc FF W mb (mb + msz) AP id a Hid).
          destruct (HXG _ Ha) as [G|G]; [left; clear - G GMSZ Hn1; lia | right; (lazymatch goal with |- ?G => let G' := eval unfold in_band, AS_LO, AS_HEAPLO in G in change_no_check G' end); clear - G GQ5 GQ6; lia]. }
      { intros a Ha. destruct (HXG _ Ha) as [G|G].
        - right; right. exists mb, (mb + msz). split; [| split; [clear - G GMSZ Hn1; lia | split]].
          + apply in_or_app. right. apply in_map_iff. exists (SCH mb n). split; [reflexivity | exact INS2].
          + destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & INN & _). pose proof (AP _ _ (all_ranges_fixed bt st _ INN)) as D. clear - D GMSZ Hn1. lia.
          + destruct (fixed_members bt st Lc FF W) as (_ & _ & _ & _ & _ & INST & _). pose proof (AP _ _ (all_ranges_fixed bt st _ INST)) as D. clear - D GMSZ Hn1. lia.
        - right; left. (lazymatch goal with |- ?G => let G' := eval unfold in_band, AS_LO, AS_HEAPLO in G in change_no_check G' end). clear - G GQ5 GQ6. lia. }
      { exists h. exact (holes_le_same_reg h st st2 eq_refl HLE). }
      { destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & Drest) & _). change (a_dep st2) with (a_dep st). clear - D1 D2 QK. lia. }
      { destruct W as (_ & _ & _ & _ & _ & _ & (D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & Drest) & _). change (a_dep st2) with (a_dep st). unfold FRW in *. clear - D9 QK. lia. }
      { exact X1. } { exact X2. } { exact X10. } { exact X11. }
      { rewrite at_u by (clear - CEILS HSr CR; lia). rewrite CP2. clear - CP16 CPlo HSr CR. Z.div_mod_to_equations. lia. }
      { rewrite at_u by (clear - CEILS HSr CR; lia). clear - CEILS G_KD. lia. }
      { rewrite at_u by (clear - CEILS HSr CR; lia). (lazymatch goal with |- ?G => let G' := eval unfold PTRHI in G in change_no_check G' end). clear - CPhi CP2. lia. }
      { apply ret_ok_lit; [clear; lia | reflexivity]. }
      { intros a Ha. rewrite at_u in Ha by (clear - CEILS HSr CR; lia). split.
        - apply GRD. apply store_ok1_heap; [clear - Ha CEILS CR G_KD; lia|]. apply CPstk. rewrite <- CP2. clear - Ha G_KD. lia.
        - eapply store_ok_mono; [exact GRD|]. apply CPstk. rewrite <- CP2. clear - Ha G_KD. lia. }
      { exact SZ8. }
      { rewrite u_Z2bv by (clear - SZ8; lia). apply Z.mod_small. clear - SZ8. lia. }
      { rewrite u_Z2bv by (clear - SZ8; lia). rewrite Z.div_small by (clear - SZ8; lia). clear. lia. }
      { exact KCW. }
      { intros i Hi. rewrite at_u in Hi by (clear - CEILS HSr CR; lia). apply GRD.
        apply store_ok1_heap; [rewrite u_Z2bv by (clear - Hi CEILS HSr CR SZ8; lia); clear - Hi CEILS CR; lia|].
        apply CPstk. rewrite u_Z2bv by (clear - Hi CEILS HSr CR SZ8; lia). rewrite <- CP2. clear - Hi SZ8. lia. }
      { rewrite at_u by (clear - CEILS HSr CR; lia). clear - CEILS CR. lia. }
      { rewrite !at_u by (clear - CEILS HSr CR; lia). clear. lia. }
      { rewrite at_u by (clear - CEILS HSr CR; lia). clear - HSr SZ8. lia. } }
    (* [comment removed for export] *)
    intros c' POST.
    destruct POST as (fx' & st' & M' & mdl' & R' & id & Ec' & HFX' & (d' & naa' & Est') & W3 & RX3 & KEPTX & DIFF2 & CHG2 & RK & A0 & Hid & SEV2 & LZ & HH2 & MW2).
    subst c'. apply CONT.
    destruct RX3 as (M0' & RP3 & DX3).
    assert (USP : U (at_ S (-2272)) = U S - 2272) by (rewrite at_u by (clear - CEILS HSr CR; lia); reflexivity).
    rewrite USP in KEPTX, CHG2.
    (* [comment removed for export] *)
    assert (KSTK : forall x : word, U S - 2272 <= U x < U S -> M' x = MD x).
    { intros x Hx. destruct (decide (M' x = MD x)) as [E|NE]; [exact E|]. exfalso.
      destruct (CHG2 x NE) as [CH|[CH|CH]].
      - clear - CH Hx. lia.
      - destruct CH as (C1 & _). clear - C1 Hx CEILS. lia.
      - rewrite BT_ia in CH. apply both_priv_lt in CH. clear - CH Hx CEILS CR. lia. }
    assert (XF : forall k bs0 (w : nat), -2272 <= k -> k + Z.of_nat w <= 0 -> rdn BSEGS MD (at_ S k) w = Some bs0 -> rdn BSEGS M' (at_ S k) w = Some bs0).
    { intros k bs0 w Hk1 Hk2 Hr. rewrite <- Hr. apply rdn_ext; [rewrite at_u by (clear - Hk1 Hk2 CEILS HSr CR; lia); clear - Hk1 Hk2 HSr; lia|].
      intros x Hx. rewrite at_u in Hx by (clear - Hk1 Hk2 CEILS HSr CR; lia). apply KSTK. clear - Hx Hk1 Hk2. lia. }
    Ltac incsD := apply in_cs; reflexivity.
    Ltac viaRKD RK k X := etransitivity; [| exact X];
      match goal with |- getr _ ?x = getr _ _ => replace x with (Z_to_bv 5 k) by (apply bv_eq; reflexivity) end; apply RK; incsD.
    (lazymatch goal with |- ?G => let G' := eval unfold runS_post in G in change_no_check G' end).
    exists fx', R', M', M0', mdl', mb, grow, d', naa', id, x18, x19.
    (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold S msz p. (lazymatch goal with |- ?G => let G' := eval unfold runS_st in G in change_no_check G' end). fold st1 st2. rewrite <- Est'.
    split; [reflexivity|]. split; [exact HFX'|]. split; [exact HH2|]. split; [exact MW2|]. split; [exact W3|]. split; [exact RP3|].
    split; [(lazymatch goal with |- ?G => let G' := eval unfold PG in G in change_no_check G' end); exact AL|]. split; [exact DY|]. split; [exact AP|].
    split.
    { (* [comment removed for export] *) rewrite Est'. (lazymatch goal with |- ?G => let G' := eval unfold depot_st in G in change_no_check G' end). (lazymatch goal with |- ?G => let G' := eval cbn [a_aa st2 st1 op_sec_alloc set_sec op_meter add_meter] in G in change_no_check G' end).
      intros a Ha. apply page_allowedb_app_l. exact (sec_naa_allowed (a_aa st ++ []) mb n ltac:(lia) ltac:(fold msz; lia) Hn1 a Ha). }
    split; [exact DX3|].
    split.
    { (* [comment removed for export] *) intros a NE. destruct (decide (M' a = MD a)) as [E|N].
      + rewrite E in NE |- *. split; [exact (PRIVfoot _ (FOOTD a NE)) | exact (DEFD a NE)].
      + destruct (DIFF2 a N) as [_ D]. split; [| exact D].
        destruct (CHG2 a N) as [CH|[CH|CH]]; [left; clear - CH G_KD; lia | right; left | right; right; exact CH].
        exact (rt_priv_sub (bt_ia bt) ((p, n) :: Lc) Lc FF (U a) (fun x Hx => or_intror Hx) CH). }
    split.
    { intros k0 v Hin.
      pose proof (ma_slotsA_range S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) k0 v Hin) as [Hk1 Hk2].
      apply (XF k0 (LE8 v) 8%nat); [clear - Hk1; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hk2; lia | exact (F_slots k0 v Hin)]. }
    split.
    { intros k0 v Hin.
      assert (Hk : -56 <= k0 /\ k0 + 8 <= 0).
      { clear - Hin. cbn [In] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      apply (XF k0 (LE8 v) 8%nat); [clear - Hk; lia | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); clear - Hk; lia | exact (F_islots k0 v Hin)]. }
    split.
    { intros a Ha. assert (D : M' a <> None).
      { destruct (decide (M' a = MD a)) as [E|N]; [| exact (proj2 (DIFF2 a N))]. rewrite E. apply GRD. apply store_ok1_heap; [clear - Ha CEILS CR; unfold MSTK_A in Ha; lia|].
        apply CPstk. rewrite <- CP2. unfold MSTK_A in Ha. clear - Ha. lia. }
      split; [exact D | exact (store_ok1_defD _ _ D)]. }
    split; [viaRKD RK 2 X2|]. split; [viaRKD RK 4 X4|]. split; [viaRKD RK 3 X3|]. split; [viaRKD RK 8 X8|]. split; [viaRKD RK 9 X9|].
    split; [exact A0|]. split; [viaRKD RK 18 X18|]. split; [viaRKD RK 19 X19|]. split; [viaRKD RK 20 X20|]. split; [viaRKD RK 21 X21|].
    split; [viaRKD RK 22 X22|]. split; [viaRKD RK 23 X23|]. split; [viaRKD RK 24 X24|]. split; [viaRKD RK 25 X25|]. split; [viaRKD RK 26 X26|].
    split; [viaRKD RK 27 X27|]. split; [exact Hid|].
    split; [exact (same_except_vm_trans _ _ _ SEV SEV2)|].
    (lazymatch goal with |- ?G => let G' := eval unfold lazy_kept in G in change_no_check G' end). rewrite ?BT_ia. (lazymatch goal with |- ?G => let G' := eval cbn [ia_img_lo ia_img_hi both_addrs] in G in change_no_check G' end).
    intros a Ha.
    assert (RNGa : 0 <= a < 2 ^ 64).
    { destruct Ha as [V|[V|V]]; [refine (proj1 (AsKSys7b.app_visible_cases bt _ Lc FF (2 ^ 20) (2 ^ 28) W a _)); rewrite ?BT_ia; exact V | clear - V CR; lia | clear - V; lia]. }
    assert (NPRIV : ~ rt_priv (bt_ia bt) Lc FF a).
    { intros (P1 & P2 & P3). rewrite BT_ia in P2, P3. cbn [ia_img_lo ia_img_hi both_addrs] in P2. destruct Ha as [V|[V|V]]; [exact (P3 V) | clear - V P1; lia | exact (P2 V)]. }
    destruct (LZ a RNGa) as [E|(blk & Hin & Hnin & Hr)].
    - rewrite E. apply (LZB a RNGa). intros (EG & F). pose proof (ROOM EG) as RM. apply NPRIV. apply (ptrarr_private bt st Lc FF W a). clear - F RM NR3. lia.
    - exfalso. apply NPRIV. apply (rt_priv_sub (bt_ia bt) ((p, n) :: Lc) Lc FF a (fun x Hx => or_intror Hx)).
      exact (OBL_store_private _ ((p, n) :: Lc) FF blk a W3 Hin Hr).
  Qed.
End TOPSD.
End WithCeil.
