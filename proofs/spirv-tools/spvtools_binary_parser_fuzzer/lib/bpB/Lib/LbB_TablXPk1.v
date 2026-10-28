(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep ContStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_DStat LbB_ContStmt LbB_ContV4 LbB_ContVot LbB_TablStmt LbB_TablOS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablPT1 LbB_TablPT2 LbB_TablPT4 LbB_TablPT6 LbB_TablPT9 LbB_TablXP1.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition expandA (t : Z) : list Z := match PrsGrammar.expand t with Some l => l | None => [] end.

Section XPk1.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.

  Definition xbud (LB : list block) (cap capm al : Z) : Prop :=
    (4 * capm <= 2 ^ 26 /\ closs cap capm <= al)
    /\ lb_small LB + 3 * 64512 <= RT_SMALL_MAX /\ Z.of_nat (length LB) + 2 <= RT_CNT_MAX /\ nlarge LB + 2 <= RT_LARGE_MAX.

  Definition pat_pre0 (ra sp tp : word) (msF : machine_state) (m : mem) (mo : Model) (s : as_St H) (LB : list block)
      (LF : list fframe) (v b cap : Z) (xs : list Z) (pid : bptr) (lo B shi STK : Z) (errv : word) : Prop :=
      vec32A LB m v b xs cap /\ v mod 8 = 0
      /\ addressable m v 24 /\ obj_win H LB LF (bv_unsigned sp) lo v 24
      /\ ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47))
      /\ wr_at asegs m v 24 /\ lb_own LB m
      /\ v4_oldblk LB b cap pid /\ (0 < cap -> SHAD m b (cc_gen (4 * cap) (4 * Zlen xs)))
      /\ as_RHEAP H s LB m /\ as_AKREL H s (mkCfg msF mo) /\ 0 <= as_AL H s
      /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF]
      /\ as_rauxv_ok H m B /\ bv_unsigned sp <= B
      /\ bv_unsigned sp mod 16 = 0 /\ bv_unsigned sp <= 2 ^ 47
      /\ stk asegs m lo (bv_unsigned sp) /\ aceil <= lo /\ lo <= bv_unsigned sp - STK
      /\ rw_cells asegs m (errno_addr tp) [C4 errv] /\ mem_inv asegs m /\ tp = Z_to_bv 64 ATP
      /\ bv_unsigned ra mod 2 = 0
      /\ ACONST m /\ as_RFS H LF m /\ (length LF < AFS_MAXLIVE_BP)%nat
      /\ stack0 m lo shi /\ bv_unsigned sp <= shi.

  Definition xp_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (msF : machine_state) (m : mem) (mo : Model)
           (s : as_St H) (LB : list block) (LF : list fframe) (t v b cap : Z) (xs : list Z) (pid : bptr)
           (lo B shi : Z) (errv : word),
      as_VIS H s msF = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                          F (Z_to_bv 64 AT_EXPAND) fc None m (seg_rom asegs) ->
      a0 = Z_to_bv 64 t -> a1 = Z_to_bv 64 v -> 0 <= t < 2 ^ 31 -> relro0 m ->
      pat_pre0 ra sp tp msF m mo s LB LF v b cap xs pid lo B shi XP_STACK errv ->
      (PrsGrammar.expand t <> None -> xbud LB cap (capmax (Zlen xs) cap 3) (as_AL H s)) ->
      as_SR H (pat_post H ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc s LB LF v b cap
                        (match PrsGrammar.expand t with Some _ => capmax (Zlen xs) cap 3 | None => cap end)
                        (xs ++ expandA t) pid lo B shi m mo
                        (fun r0 => r0 = Z_to_bv 64 (match PrsGrammar.expand t with Some _ => 1 | None => 0 end)))
        (mkCfg msF mo).

  Record xpent : Type := XPEnt {
    x_ra : word; x_sp : word; x_gp : word; x_tp : word;
    x_s0 : word; x_s1 : word; x_s2 : word; x_s3 : word; x_s4 : word; x_s5 : word;
    x_s6 : word; x_s7 : word; x_s8 : word; x_s9 : word; x_s10 : word; x_s11 : word;
    x_F : bvmap 5 word; x_fc : bv 32; x_m : mem; x_mo : Model;
    x_s : as_St H; x_LB : list block; x_LF : list fframe;
    x_t : Z; x_v : Z; x_b : Z; x_cap : Z; x_xs : list Z; x_pid : bptr;
    x_lo : Z; x_B : Z; x_shi : Z; x_ff : Z; x_fp : Z }.

  Definition xSP (e : xpent) : Z := bv_unsigned (x_sp e).

  Definition xS1 (e : xpent) : Z := xSP e - 160 - (xSP e - 160) mod 32.

  Definition xcapm (e : xpent) : Z := match PrsGrammar.expand (x_t e) with Some _ => capmax (Zlen (x_xs e)) (x_cap e) 3 | None => x_cap e end.
  Definition xLF (e : xpent) : list fframe := (2, x_ff e, x_fp e) :: x_LF e.

  Definition xXS (e : xpent) : list (Z * Z) :=
    [(as_FSB H, as_FSB H + AFS_FLAGS); (x_fp e, x_fp e + 1); (x_ff e, x_ff e + 256); (sh (x_ff e), sh (x_ff e) + 32)].
  Definition xXE (e : xpent) : list (Z * Z) := (x_v e, x_v e + 24) :: v4_oldx (x_b e) (4 * x_cap e) ++ xXS e.
  Definition xsaved (e : xpent) : list cell :=
    [C8 (x_s11 e); C8 (x_s10 e); C8 (x_s9 e); C8 (x_s8 e); C8 (x_s7 e); C8 (x_s6 e); C8 (x_s5 e); C8 (x_s4 e);
     C8 (x_s3 e); C8 (x_s2 e); C8 (x_s1 e); C8 (x_s0 e); C8 (x_ra e)].

  Definition xg (e : xpent) (bi capi : Z) (ys : list Z) : xgeo :=
    XG (xSP e) (xS1 e) (x_ff e) (x_v e) bi (bi + 4 * Zlen ys) (bi + 4 * capi).

  Definition XV (e : xpent) : Prop := PrsGrammar.expand (x_t e) <> None.

  Definition xpre (e : xpent) : Prop :=
    let SP := xSP e in let v := x_v e in let LB := x_LB e in let LF := x_LF e in let lo := x_lo e in
       fresh_frame H LF 2 (x_ff e) (x_fp e) /\ (length LF < AFS_MAXLIVE_BP)%nat
    /\ (forall f, In f LF -> aframe_range H (ff_class f) (ff_addr f) (ff_flag f))
    /\ SP mod 16 = 0 /\ SP <= 2 ^ 47 /\ SP <= x_B e /\ SP <= x_shi e /\ aceil <= lo /\ lo <= SP - XP_STACK
    /\ x_tp e = Z_to_bv 64 ATP /\ bv_unsigned (x_ra e) mod 2 = 0

    /\ 0 <= x_t e < 2 ^ 31 /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_RREF] /\ True /\ True /\ True /\ True
    /\ v mod 8 = 0 /\ ((0x6e8000 <= v /\ v + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= v /\ v + 24 <= 2 ^ 47))
    /\ obj_win H LB LF SP lo v 24
    /\ v4_oldblk LB (x_b e) (x_cap e) (x_pid e) /\ List.NoDup (map blk_id LB) /\ as_RHEAP H (x_s e) LB (x_m e)

    /\ (XV e -> 4 * xcapm e <= 2 ^ 26 /\ closs (x_cap e) (xcapm e) <= as_AL H (x_s e))
    /\ (XV e -> lb_small LB + 3 * 64512 <= RT_SMALL_MAX)
    /\ (XV e -> Z.of_nat (length LB) + 2 <= RT_CNT_MAX) /\ (XV e -> nlarge LB + 2 <= RT_LARGE_MAX)
    /\ trace_ok (as_TR H) APC0_FREE [v4_del_ra VOT_SLOW_CREF] /\ 0 <= as_AL H (x_s e)
    /\ 0 <= Zlen (x_xs e) <= x_cap e /\ (x_b e = 0 -> x_cap e = 0)
    /\ ((0 <= x_b e /\ x_b e + 4 * x_cap e <= 0x7fff7000) \/ (0x10007fff8000 <= x_b e /\ x_b e + 4 * x_cap e <= 2 ^ 47))
    /\ (x_b e <> 0 -> v + 24 <= x_b e \/ x_b e + 4 * x_cap e <= v).

  Definition xgrown (e : xpent) (LBi : list block) (bi capi : Z) (pidi : bptr) : Prop :=
    (capi = x_cap e /\ bi = x_b e /\ LBi = x_LB e /\ pidi = x_pid e)
    \/ (x_cap e < capi <= xcapm e /\ LBi = v4_newLB H (x_LB e) (x_b e) (x_pid e) pidi bi (4 * capi)
        /\ ablock_range H bi (4 * capi)).

  Definition xframe (e : xpent) (mL : mem) (sL : as_St H) (LBi : list block) (eL : word) : Prop :=
    let SP := xSP e in let ff := x_ff e in let fp := x_fp e in
       mem_inv asegs mL /\ ACONST mL /\ stk asegs mL (x_lo e) SP /\ stack0 mL (x_lo e) (x_shi e)
    /\ rw_cells asegs mL (errno_addr (x_tp e)) [C4 eL] /\ as_rauxv_ok H mL (x_B e)
    /\ rw_cells asegs mL (SP - 104) (xsaved e) /\ rw_cells asegs mL (ff + 32) [C4 (Z_to_bv 64 (x_t e))]
    /\ rw_cells asegs mL (ff + 248) [C8 (Z_to_bv 64 fp)] /\ wr_at asegs mL ff 256 /\ wr_at asegs mL (sh ff) 32 /\ wr_at asegs mL fp 1
    /\ wr_at asegs mL (ff + 32) 4 /\ rw_cells asegs mL (sh ff + 4) [C1 (b8 4)]
    /\ as_RFS H (xLF e) mL /\ as_RHEAP H sL LBi mL /\ lb_own LBi mL.

  Definition xslotP (e : xpent) (sv : option bool) (mL : mem) : Prop :=
    match sv with None => True | Some bA => xslotc bA (xg e 0 0 []) mL end.

  Definition xvec (e : xpent) (ys : list Z) (mL : mem) (LBi : list block) (bi capi : Z) (pidi : bptr) : Prop :=
    let v := x_v e in
       vec32A LBi mL v bi ys capi /\ (0 < capi -> SHAD mL bi (cc_gen (4 * capi) (4 * Zlen ys)))
    /\ addressable mL v 24 /\ wr_at asegs mL v 24
    /\ v4_oldblk LBi bi capi pidi /\ xgrown e LBi bi capi pidi.

  Definition xmem (e : xpent) (ys : list Z) (sv : option bool) (mL : mem) (sL : as_St H) (LBi : list block) (bi capi : Z)
      (pidi : bptr) (eL : word) : Prop :=
       xframe e mL sL LBi eL /\ xslotP e sv mL /\ xvec e ys mL LBi bi capi pidi
    /\ xpres H (x_LB e) (xSP e) (xXE e) (x_m e) mL
    /\ as_AL H sL >= as_AL H (x_s e) - closs (x_cap e) capi.

  Definition xat (e : xpent) (pc : Z) (RL : xgeo -> list rrole) (ys : list Z) (sv : option bool) (cf : config) : Prop :=
    exists R mL sL LBi bi capi pidi eL,
      as_VIS H sL (cfg_ms cf) = MS R (x_F e) (Z_to_bv 64 pc) (x_fc e) None mL (seg_rom asegs) /\ rfull R
      /\ getr R 3 = x_gp e /\ getr R 4 = x_tp e /\ RPl (xcommon (xg e bi capi ys) ++ RL (xg e bi capi ys)) R
      /\ as_AKREL H sL cf /\ as_MPRES H (x_mo e) (cfg_model cf)
      /\ xmem e ys sv mL sL LBi bi capi pidi eL.

  Definition xok0 (e : xpent) (LBi : list block) (iv : Z * Z) : Prop :=
    aclient_write_ok H LBi iv /\ afs_write_ok H (xLF e) iv /\ aconst_ok iv /\ stack0_ok iv
    /\ (snd iv <= ATP - 164 \/ ATP - 160 <= fst iv)
    /\ (snd iv <= xSP e - 104 \/ xSP e <= fst iv)
    /\ (snd iv <= x_ff e + 32 \/ x_ff e + 36 <= fst iv)
    /\ (snd iv <= x_ff e + 248 \/ x_ff e + 256 <= fst iv)
    /\ (snd iv <= sh (x_ff e) + 4 \/ sh (x_ff e) + 5 <= fst iv).
End XPk1.
Arguments x_ra {H} _. Arguments x_sp {H} _. Arguments x_gp {H} _. Arguments x_tp {H} _.
Arguments x_s0 {H} _. Arguments x_s1 {H} _. Arguments x_s2 {H} _. Arguments x_s3 {H} _. Arguments x_s4 {H} _.
Arguments x_s5 {H} _. Arguments x_s6 {H} _. Arguments x_s7 {H} _. Arguments x_s8 {H} _. Arguments x_s9 {H} _.
Arguments x_s10 {H} _. Arguments x_s11 {H} _. Arguments x_F {H} _. Arguments x_fc {H} _. Arguments x_m {H} _.
Arguments x_mo {H} _. Arguments x_s {H} _. Arguments x_LB {H} _. Arguments x_LF {H} _. Arguments x_t {H} _.
Arguments x_v {H} _. Arguments x_b {H} _. Arguments x_cap {H} _. Arguments x_xs {H} _. Arguments x_pid {H} _.
Arguments x_lo {H} _. Arguments x_B {H} _. Arguments x_shi {H} _. Arguments x_ff {H} _. Arguments x_fp {H} _.
Arguments XV {H} _. Arguments xSP {H} _. Arguments xS1 {H} _. Arguments xcapm {H} _. Arguments xLF {H} _. Arguments xsaved {H} _. Arguments xg {H} _ _ _ _.

Section XPgeo.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HB : asan_rt_hyps H.

  Definition xgeoP (e : xpent H) : Prop :=
       xSP e mod 16 = 0 /\ 2 ^ 45 <= xS1 e /\ xS1 e mod 32 = 0 /\ xS1 e + 160 <= xSP e /\ xSP e - 176 <= xS1 e /\ xSP e <= 2 ^ 47
    /\ aceil <= x_lo e /\ x_lo e + XP_STACK - 192 <= xS1 e
    /\ x_ff e mod 64 = 0 /\ 0x6e8000 + 0x9000 <= x_ff e /\ x_ff e + 256 <= aceil
    /\ as_FSB H + 0x1000 <= x_fp e /\ x_fp e < as_FSB H + 0x9000 /\ as_FSB H + 0x9000 <= x_ff e
    /\ x_ff e + 256 <= as_FSB H + AFS_SIZE
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil
    /\ sh (x_ff e) + 32 = sh (x_ff e + 256) /\ 0x7fff8000 <= sh (x_ff e) /\ sh (x_ff e) + 32 <= 0x10007fff8000
    /\ (sh (x_ff e) + 32 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh (x_ff e))
    /\ (x_ff e + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= x_ff e) /\ (x_fp e + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= x_fp e)
    /\ x_v e mod 8 = 0 /\ ((0x6e8000 <= x_v e /\ x_v e + 24 <= 0x7fff7000) \/ (0x10007fff8000 <= x_v e /\ x_v e + 24 <= 2 ^ 47))
    /\ (x_v e + 24 <= x_lo e \/ xSP e <= x_v e) /\ (x_v e + 24 <= x_ff e \/ x_ff e + 256 <= x_v e)
    /\ (x_v e + 24 <= as_FSB H \/ as_FSB H + 0x9000 <= x_v e) /\ (x_v e + 24 <= x_fp e \/ x_fp e + 1 <= x_v e)
    /\ 0x7fff8000 <= sh (x_v e) /\ sh (x_v e) + 3 <= 0x10007fff8000
    /\ 0 <= x_t e < 2 ^ 31 /\ x_tp e = Z_to_bv 64 ATP.

  Lemma x2frame_facts : forall LF ff fp, fresh_frame H LF 2 ff fp ->
       0x6e8000 + 0x9000 <= ff /\ ff + 256 <= aceil /\ ff mod 64 = 0
    /\ as_FSB H + 0x1000 <= fp /\ fp < as_FSB H + 0x9000 /\ as_FSB H + 0x9000 <= ff /\ ff + 256 <= as_FSB H + AFS_SIZE
    /\ 0x6e8000 <= as_FSB H /\ as_FSB H + AFS_SIZE <= aceil /\ aapp (as_FSB H) AFS_SIZE
    /\ sh ff + 32 = sh (ff + 256) /\ sh (as_FSB H) <= sh ff /\ sh (ff + 256) <= sh (as_FSB H + AFS_SIZE)
    /\ 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000
    /\ (sh ff + 32 <= as_FSB H \/ as_FSB H + AFS_SIZE <= sh ff)
    /\ (ff + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) /\ (fp + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fp).
  Proof.
    intros LF ff fp FF. pose proof (fresh_frame_facts H LF 2 ff fp FF) as (K & R1 & R2 & M64 & M8 & P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
    change (fsz 2) with 256 in *. unfold AIMG_TOP, AFS_HDR, AFS_FLAGS in *.
    pose proof aceil_facts as ACF.
    assert (S1 : sh ff + 32 = sh (ff + 256)) by (unfold sh; Z.div_mod_to_equations; lia).
    assert (S2 : sh (as_FSB H) <= sh ff) by (apply sh_mono; lia).
    assert (S3 : sh (ff + 256) <= sh (as_FSB H + AFS_SIZE)) by (apply sh_mono; lia).
    assert (S4 : 0x7fff8000 <= sh ff /\ sh ff + 32 <= 0x10007fff8000)
      by (unfold sh; rewrite ASHADOW_BASE_val; unfold AFS_SIZE in *; Z.div_mod_to_equations; lia).
    pose proof (aapp_disjoint_sh (as_FSB H) AFS_SIZE ff 256 P9 ltac:(lia) ltac:(unfold AAPP_HI; lia) ltac:(lia)) as S5.
    change (nsh 256) with 32 in S5.
    assert (BA : (ff + 256 <= 0x7fff7000 \/ 0x10007fff8000 <= ff) /\ (fp + 1 <= 0x7fff7000 \/ 0x10007fff8000 <= fp)).
    { clear - P9 P5 P6 P3 P4. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP, AFS_SIZE in *. lia. }
    repeat split; try assumption; try lia; tauto.
  Qed.

  Lemma xgeoP_of : forall e, xpre H e -> xgeoP e.
  Proof.
    intros e P. destruct P as (FF & LFL & LFR & SP16 & SPH & SPB & SPS & CE & LO & TP & RA & TR & _ & _ & _ & _ & _ & V8 & VB & OBJ & OLD & BUD).
    clear OLD BUD.
    pose proof (x2frame_facts _ _ _ FF) as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & G10 & G11 & G12 & G13 & G14 & G15 & G16 & G17 & G18).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    destruct OBJ as (_ & _ & _ & FW & _ & SD).
    assert (VFF : (x_v e + 24 <= x_ff e \/ x_ff e + 256 <= x_v e)
                  /\ (x_v e + 24 <= as_FSB H \/ as_FSB H + 0x9000 <= x_v e) /\ (x_v e + 24 <= x_fp e \/ x_fp e + 1 <= x_v e)).
    { clear - FW FF LFR G4 G5 G6 G7. unfold afs_write_ok in FW. cbn [fst snd] in FW.
      destruct FF as (_ & _ & FD).
      destruct FW as [(F1 & F2)|(f & Hf & F1 & F2)].
      - unfold AFS_SIZE, AFS_FLAGS in *. lia.
      - destruct (FD f Hf) as [D1 D2]. change (fsz 2) with 256 in D1.
        destruct (LFR f Hf) as (_ & R1 & R2 & _).
        clear - D1 R1 R2 F1 F2 G4 G5 G6 G7. unfold AFS_HDR, AFS_FLAGS, AFS_SIZE in *. lia. }
    clear FW LFR.
    assert (SHV : 0x7fff8000 <= sh (x_v e) /\ sh (x_v e) + 3 <= 0x10007fff8000).
    { clear - VB. unfold sh. rewrite ASHADOW_BASE_val. destruct VB; Z.div_mod_to_equations; lia. }
    assert (SPR : 2 ^ 45 <= xSP e - 176)
      by (clear - LO CE ACF1; unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in LO; lia).
    assert (S1R : xSP e - 176 <= xS1 e /\ xS1 e + 160 <= xSP e /\ xS1 e mod 32 = 0)
      by (unfold xS1; clear - SP16; Z.div_mod_to_equations; lia).
    destruct VFF as (VF1 & VF2 & VF3).
    unfold xgeoP. unfold AFS_SIZE in *.
    vhide VB. vhide G16. vhide G17. vhide G18. vhide SD. vhide VF1. vhide VF2. vhide VF3. vhide G10.
    split; [exact SP16|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [exact SPH|].
    split; [exact CE|]. split; [clear - S1R LO; unfold XP_STACK, AFS_STACK, AINTRIN_STACK, V4_STACK, AOPNEW_STACK, AMALLOC_STACK in *; lia|].
    split; [exact G3|]. split; [lia|]. split; [lia|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exact G11|]. split; [lia|]. split; [lia|]. split; [destruct G16 as [X]; exact X|].
    split; [destruct G17 as [X]; exact X|]. split; [destruct G18 as [X]; exact X|].
    split; [exact V8|]. split; [destruct VB as [X]; exact X|]. split; [destruct SD as [X]; exact X|].
    split; [destruct VF1 as [X]; exact X|]. split; [destruct VF2 as [X]; exact X|]. split; [destruct VF3 as [X]; exact X|].
    split; [lia|]. split; [lia|]. split; [exact TR|]. exact TP.
  Qed.
End XPgeo.
