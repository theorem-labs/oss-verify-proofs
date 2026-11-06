(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import Tac Bytes Arr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import StepA StepA2 SysStepA AImages.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.SpecA Require Import AsanState AsanFakeStack.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.B Require Import BM_kit BI_shadow BF_kit BF_fakestack_rep BF_fakestack.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Zify.zify_internal_to_euclidean_division_equations ::= OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA.LiaFastA.zify_fast_euclid3.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Ltac showpc := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc end.
Ltac showregs := match goal with |- evtA _ _ _ (MS ?R _ ?pc _ _ _ _) => idtac "=== PC" pc R end.
Ltac cstep := zstepA; try first [if_true | if_false].

From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib Require Import RunCeiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac lia ::=
  first [ LiaTuning.zify_prune; LiaTuning.zify_noeuclid; Z.euclidean_division_equations_cleanup; xlia zchecker
        | LiaTuning.zify_prune; Zify.zify; xlia zchecker
        | Zify.zify; xlia zchecker ].
(* [comment removed for export] *)
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.LibA Require Import SecRanges.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= force_section_ranges.   (* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac aceil :=
  lazymatch goal with
  | H : _ <= alloc_ceiling <= _ |- _ => idtac
  | |- context [alloc_ceiling] => repeat match goal with H : True |- _ => clear H end; pose proof alloc_ceiling_range as CEILB
  | H : context [alloc_ceiling] |- _ => repeat match goal with H' : True |- _ => clear H' end; pose proof alloc_ceiling_range as CEILB
  | _ => first [ pose proof I as CEILB | idtac ]
  end.
Section RC__1.
Context {RC__ : OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Lib.RunCeiling.RunCeiling}.
Definition SM1 : Z := 0x3e110.
(* [comment removed for export] *)
Definition sm1_tail_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo fsbase pos : Z) : machine_state -> Prop :=
  fun ms' => exists (t0' a1' a2' a3' a4' a5' a6' a7' : word) (m' : mem) (hv : word) (j1 j2 : list byte),
    ms' = MS (mkR ra sp gp tp t0' t1 t2 s0 s1 (Z_to_bv 64 (ff1 fsbase pos)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (sm1_W sp fsbase pos) m m' /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ rw_cells bsegs m' (fsbase + 8) [C8 hv]
    /\ rw_cells bsegs m' (fl1 fsbase pos) [C1 (Z_to_bv 8 1)]
    /\ rw_cells bsegs m' (ff1 fsbase pos) [CB 24 j1; C8 sp; CB 88 j2; C8 (Z_to_bv 64 (fl1 fsbase pos))]
    /\ rw_cells bsegs m' (sh1 fsbase pos) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)].

(* [comment removed for export] *)
Definition sm1_post (ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo fsbase : Z) (LF : list (Z * Z)) (p0 p1 : Z) : machine_state -> Prop :=
  fun ms' => exists pos, (pos = p0 \/ pos = p1) /\ lf_mem LF 1 (fs_frame_addr fsbase 1 pos) = false
    /\ sm1_tail_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fsbase pos ms'.

Section SMW.
Variable P : acc -> Prop.

(* [comment removed for export] *)
Ltac sm1_tail_tac G2 G3 G4 EFa PR :=
  cstep; cstep; cstep; cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  cstep; cstep; (* [comment removed for export] *)
  cstep; cstep; cstep; (* [comment removed for export] *)
  rewrite Z.shiftl_mul_pow2 by lia; change (2 ^ 7) with 128;
  lazymatch goal with |- context [Z_to_bv 64 (?fsb + 36864 + (1048576 + ?pp * 128))] =>
    lazymatch goal with E : ?Fv = fsb + 1085440 + 128 * pp |- _ =>
      replace (fsb + 36864 + (1048576 + pp * 128)) with Fv by lia end end;
  cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  lazymatch goal with IG : icp_globals bsegs ?m0 ?SB |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with MUx : munch _ m0 mx, WMx : wmono bsegs m0 mx |- _ =>
      pose proof (icp_globals_transport bsegs _ m0 mx SB IG MUx WMx) as IGx end end;
  lazymatch goal with IGy : ?d -> icp_globals _ _ _ |- _ =>
    assert (DJ : d) by (cbn; repeat split; try exact I; left; lia); specialize (IGy DJ) end;
  lazymatch goal with E : ?SBv = 2147450880 |- _ => subst SBv end;
  callA (mts2_walk P); [ eassumption | eassumption | | eassumption | reflexivity | ];
  [ unfold a_in_mem2, a_high_mem, A_HIGHEND_VAL; clear -G2 G3 G4 EFa PR; aceil; lia |];
  lazymatch goal with ESa' : 2147450880 + Z.shiftr ?Fa 3 = ?Sa |- _ => rewrite ESa' end;
  cstep; cstep; cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  do 4 cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  cstep; (* [comment removed for export] *)
  lazymatch goal with H : rw_cells bsegs ?mx (bv_unsigned ?spv + -32) _ |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
    lazymatch goal with S : stk bsegs mx ?lo _ |- _ => release_frame H S (bv_unsigned spv) end end;
  lazymatch goal with Q8 : ?fsb = ?q * 8 |- _ =>
    assert (forall p, (fsb + 1085440 + 128 * p) / 8 = q + 135680 + 16 * p) by (intros; rewrite Q8; Z.div_mod_to_equations; lia) end;
  repeat match goal with E : ?X = ?fsb + 1085440 + 128 * ?pp |- _ => subst X end;
  repeat match goal with E : ?X = ?fsb + 20480 + ?pp |- _ => subst X end;
  repeat match goal with E : ?X = 2147450880 + ?q + 135680 + 16 * ?pp |- _ => subst X end;
  finishA;
  first [ eassumption
        | unfold ff1, fl1; eassumption
        | match goal with |- rw_cells _ ?mm (sh1 _ _) [C8 _; C8 _] =>
            match goal with S : rw_cells _ mm ?b [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 0)] |- rw_cells _ _ ?a _ =>
              replace a with b by (unfold sh1, ff1; Z.div_mod_to_equations; lia); exact S end end
        | match goal with |- rw_cells _ ?mm (sh1 _ _) [CB 16 _] =>
            match goal with S : rw_cells _ mm ?b [CB 16 _] |- rw_cells _ _ ?a _ =>
              replace a with b by (unfold sh1, ff1; Z.div_mod_to_equations; lia); exact S end end
        | match goal with H : forall p : Z, _ = _ |- munch _ _ _ => unfold sm1_W; unfold sh1; unfold fl1, ff1; rewrite !H; eassumption end
        | idtac ].

(* [comment removed for export] *)
Lemma sm1_tail :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (xt0 xa0 xa2 xa6 : word) (F : bvmap 5 word) (fc : bv 32) (m mX : mem) (lo fsbase pos : Z) (SB : Z)
         (hv0 : word) (jf js : list byte),
  let Fa := fsbase + 1085440 + 128 * pos in let La := fsbase + 20480 + pos in let Sa := 2147450880 + Fa / 8 in
  0 <= pos < 8192 ->
  alloc_ceiling <= lo -> lo <= bv_unsigned sp - 208 -> bv_unsigned sp <= 2^47 ->
  fsbase mod 4096 = 0 -> 0x603000 <= fsbase -> fsbase + kFsBytes <= alloc_ceiling ->
  (fsbase + kFsBytes <= FS_SB - 4096 \/ FS_SB + 2^44 <= fsbase) -> SB = FS_SB ->
  mem_inv bsegs mX -> icp_globals bsegs m SB -> munch (sm1_W sp fsbase pos) m mX -> wmono bsegs m mX ->
  stk bsegs mX lo (bv_unsigned sp - 32) ->
  rw_cells bsegs mX (bv_unsigned sp + -32) [C8 s2; C8 s1; C8 s0; C8 ra] ->
  rw_cells bsegs mX (fsbase + 8) [C8 hv0] ->
  rw_cells bsegs mX La [C1 (Z_to_bv 8 0)] ->
  rw_cells bsegs mX Fa [CB 128 jf] ->
  rw_cells bsegs mX Sa [CB 16 js] ->
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, fsbase <= a -> a + Z.of_nat k <= fsbase + kFsBytes -> P (Z_to_bv 64 a, k)) ->
  (forall a k, FS_SB + fsbase / 8 <= a -> a + Z.of_nat k <= FS_SB + (fsbase + kFsBytes) / 8 -> P (Z_to_bv 64 a, k)) ->
  evtA bsegs P (sm1_tail_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fsbase pos)
    (MS (mkR (Z_to_bv 64 0x3e134) (Z_to_bv 64 (bv_unsigned sp + -32)) gp tp xt0 t1 t2 sp (Z_to_bv 64 fsbase)
             xa0 (Z_to_bv 64 (fsbase + 4096)) xa2 (Z_to_bv 64 (fsbase + 20480)) (Z_to_bv 64 8191) (Z_to_bv 64 La) xa6 (Z_to_bv 64 pos)
             (Z_to_bv 64 20) s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x3e21c) fc None mX (seg_rom bsegs)).
Proof. aceil.
  intros until js. intros Fa La Sa PR LOC LO SPH G1 G2 G3 G4 ESB MI IG MU WM ST FR HINT FL FRM SH PSTK PIMG PFS PFSH.
  pose proof LOC as LOC'. aceil. unfold kFsBytes, FS_SB in *.
  assert (EFa : Fa = fsbase + 1085440 + 128 * pos) by reflexivity.
  assert (ELa : La = fsbase + 20480 + pos) by reflexivity.
  assert (ESa : Sa = 2147450880 + Fa / 8) by reflexivity.
  clearbody Fa La Sa.
  destruct (proj1 (Z.mod_divide fsbase 8 ltac:(lia)) ltac:(Z.div_mod_to_equations; lia)) as [q Q8].
  assert (DP : forall p, (fsbase + 1085440 + 128 * p) / 8 = q + 135680 + 16 * p) by (intros; rewrite Q8; Z.div_mod_to_equations; lia).
  assert (ESa2 : Sa = 2147450880 + q + 135680 + 16 * pos) by (rewrite ESa, EFa, DP; lia).
  assert (ESa' : 2147450880 + Z.shiftr Fa 3 = Sa) by (rewrite Z.shiftr_div_pow2, EFa, ESa2 by lia; change (2 ^ 3) with 8; rewrite DP; lia).
  unfold sm1_W in MU. unfold sh1 in MU. unfold fl1, ff1 in MU. rewrite !DP in MU.
  assert (FA8 : Fa mod 8 = 0).
  { replace Fa with ((q + 135680 + 16 * pos) * 8) by lia. apply Z_mod_mult. }
  clear ESa DP.
  sm1_tail_tac G2 G3 G4 EFa PR.
  all: lazymatch goal with |- ?g => idtac "TAILGOAL" g end.
Qed.

Lemma stack_malloc1_walk :
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (E : aenv) (fsbase : Z) (pl : fs_plumb) (fs : fsstate) (LF : list (Z * Z)) (SB : Z)
         (h : word),
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - 208 -> bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 ->
  mem_inv bsegs m -> tp = Z_to_bv 64 FS_TP ->
  FSEnv bsegs E fsbase pl m -> FSRep bsegs E fsbase fs LF m -> icp_globals bsegs m SB -> SB = FS_SB ->
  rw_cells bsegs m (fsbase + 8) [C8 h] ->
  (forall f f', In (1, f) LF -> In (1, f') LF -> f = f') ->
  (forall a k, lo <= a -> a + Z.of_nat k <= bv_unsigned sp -> P (Z_to_bv 64 a, k)) ->
  (forall a k, 0x10000 <= a -> a + Z.of_nat k <= 0x603000 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, fp_ctx pl <= a -> a + Z.of_nat k <= fp_ctx pl + 160 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, ae_thread E <= a -> a + Z.of_nat k <= ae_thread E + 64 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, fp_dtls pl <= a -> a + Z.of_nat k <= fp_dtls pl + 4096 -> P (Z_to_bv 64 a, k)) ->
  (forall a k, fsbase <= a -> a + Z.of_nat k <= fsbase + kFsBytes -> P (Z_to_bv 64 a, k)) ->
  (forall a k, FS_SB + fsbase / 8 <= a -> a + Z.of_nat k <= FS_SB + (fsbase + kFsBytes) / 8 -> P (Z_to_bv 64 a, k)) ->
  let uh := bv_unsigned h in let p0 := Z.land uh 8191 in let p1 := Z.land ((uh + 1) mod 2^64) 8191 in
  evtA bsegs P (sm1_post ra sp gp tp t1 t2 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo fsbase LF p0 p1)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 SM1) fc None m (seg_rom bsegs)).
Proof. aceil.
  intros until h. intros ST LOC LO SPH AL MI Htp ENV FS IG ESB HINT UNIQ PSTK PIMG PCTX PTHR PDT PFS PFSH uh p0 p1.
  pose proof ENV as (DESC & REAL & INI & DTV & DTV1 & TLS & KI & KEY & TSD & TSD0 & CTXT & THR & (cf & vb & dto & GF & CF & GV & VB & GD & DT & CF1 & CF2 & VB1 & VB2 & DT1 & DT2 & PinCF & PinVB & PinDT) & DTVE & NZ & DVR & DL0 & DL1 & DL8 & C0 & C1 & C8 & T0 & T1 & T8 & GSB & SBV).
  pose proof FS as (G1 & G2 & G3 & G4 & HH & HL & HG & HF & HW & ND & HLF).
  unfold SM1 in *. pose proof LOC as LOC'. pose proof G3 as G3'. pose proof G4 as G4'.
  aceil. unfold kFsBytes, FS_SB in *.
  (* [comment removed for export] *)
  pose proof (bv_unsigned_in_range 64 h) as UHR. unfold bv_modulus in UHR. cbn in UHR. fold uh in UHR.
  assert (P0 : 0 <= p0 < 8192).
  { subst p0. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. change 8192 with (2 ^ 13). apply Z.mod_pos_bound. lia. }
  assert (P1 : 0 <= p1 < 8192).
  { subst p1. change 8191 with (Z.ones 13). rewrite Z.land_ones by lia. change 8192 with (2 ^ 13). apply Z.mod_pos_bound. lia. }
  assert (P01 : p0 <> p1).
  { subst p0 p1. change 8191 with (Z.ones 13). rewrite !Z.land_ones by lia.
    change (2 ^ 64) with (2 ^ 13 * 2 ^ 51). rewrite Z.rem_mul_r by lia. change (2 ^ 13) with 8192.
    intros EQ. Z.div_mod_to_equations. lia. }
  assert (K0 : fs_pos_ok 1 p0) by (split; [lia| unfold fs_nframes, kFsLog, kFsMinFrameLog; cbn; lia]).
  assert (K1 : fs_pos_ok 1 p1) by (split; [lia| unfold fs_nframes, kFsLog, kFsMinFrameLog; cbn; lia]).
  pose proof (HF 1 p0 K0) as FL0. rewrite fl1_eq in FL0. unfold fl1 in FL0.
  pose proof (HF 1 p1 K1) as FL1. rewrite fl1_eq in FL1. unfold fl1 in FL1.
  destruct (HW 1 p0 K0) as [FRS0 SHS0]. rewrite sh1_eq in SHS0. rewrite ff1_eq in FRS0. unfold sh1 in SHS0. unfold ff1, fs_frame_bytes, kFsMinFrameLog in FRS0, SHS0.
  destruct (HW 1 p1 K1) as [FRS1 SHS1]. rewrite sh1_eq in SHS1. rewrite ff1_eq in FRS1. unfold sh1 in SHS1. unfold ff1, fs_frame_bytes, kFsMinFrameLog in FRS1, SHS1.
  change (2 ^ (6 + 1)) with 128 in FRS0, SHS0, FRS1, SHS1. change (128 / 8) with 16 in SHS0, SHS1.
  destruct (stk_carve bsegs _ _ _ 128 FRS0 ltac:(lia)) as [_ [jf0 FR0]]. clear FRS0.
  destruct (stk_carve bsegs _ _ _ 128 FRS1 ltac:(lia)) as [_ [jf1 FR1]]. clear FRS1.
  destruct (stk_carve bsegs _ _ _ 16 SHS0 ltac:(lia)) as [_ [js0 SH0]]. clear SHS0.
  destruct (stk_carve bsegs _ _ _ 16 SHS1 ltac:(lia)) as [_ [js1 SH1]]. clear SHS1.
  match type of FR0 with rw_cells _ _ ?a _ => replace a with (fsbase + 1085440 + 128 * p0) in FR0 by lia end.
  match type of FR1 with rw_cells _ _ ?a _ => replace a with (fsbase + 1085440 + 128 * p1) in FR1 by lia end.
  match type of SH0 with rw_cells _ _ ?a _ => replace a with (2147450880 + (fsbase + 1085440 + 128 * p0) / 8) in SH0 by lia end.
  match type of SH1 with rw_cells _ _ ?a _ => replace a with (2147450880 + (fsbase + 1085440 + 128 * p1) / 8) in SH1 by lia end.
  (* [comment removed for export] *)
  assert (LM01 : lf_mem LF 1 (fs_frame_addr fsbase 1 p0) = true -> lf_mem LF 1 (fs_frame_addr fsbase 1 p1) = false).
  { intros L0. destruct (lf_mem LF 1 (fs_frame_addr fsbase 1 p1)) eqn:L1; [| reflexivity]. exfalso.
    apply lf_mem_In in L0. apply lf_mem_In in L1. pose proof (UNIQ _ _ L0 L1) as EQ. rewrite !ff1_eq in EQ. unfold ff1 in EQ. lia. }
  assert (D0 : (fsbase + 1085440 + 128 * p0) / 8 = fsbase / 8 + 135680 + 16 * p0) by (Z.div_mod_to_equations; lia).
  assert (D1 : (fsbase + 1085440 + 128 * p1) / 8 = fsbase / 8 + 135680 + 16 * p1) by (Z.div_mod_to_equations; lia).
  assert (Q8 : fsbase = 8 * (fsbase / 8)) by (Z.div_mod_to_equations; lia).
  rewrite D0 in SH0. rewrite D1 in SH1.
  assert (SEP : p0 + 1 <= p1 \/ p1 + 1 <= p0) by lia.
  assert (MU : munch [(bv_unsigned sp - 208, bv_unsigned sp)] m m) by apply munch_refl.
  assert (WM : wmono bsegs m m) by apply wmono_refl.
  set (La0 := fsbase + 20480 + p0) in *. set (La1 := fsbase + 20480 + p1) in *.
  unfold FS_TP, kFsLog in *.
  carve_frame 32%nat ST.
  cstep. (* [comment removed for export] *)
  do 4 cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  call_spA (tga_icp_walk P);
    [ eassumption | exact LOC' | lia | lia | eassumption | exact Htp | reflexivity | | intros a k Ha Hk; apply PSTK; lia | exact PIMG | exact PCTX | exact PTHR | exact PDT | ].
  { unfold FSEnv, FS_TP. repeat match goal with |- _ /\ _ => split end; try eassumption; try lia.
    exists cf, vb, dto. repeat match goal with |- _ /\ _ => split end; try eassumption; try lia. }
  unfold FS_TP in *.
  clear DESC REAL INI DTV DTV1 KI KEY TSD TSD0 CTXT THR GF CF GV VB GD DT DTVE GSB SBV.
  cstep. (* [comment removed for export] *)
  clear TLS.
  cstep. (* [comment removed for export] *) if_cases KB; zify_cond KB; try (exfalso; lia).
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  cstep. (* [comment removed for export] *)
  fold uh. fold p0. fold La0.
  unfold flag_byte in FL0, FL1. destruct (lf_mem LF 1 (fs_frame_addr fsbase 1 p0)) eqn:LM0; cbn [Z.b2z] in FL0.
  - (* [comment removed for export] *)
    rewrite (LM01 eq_refl) in FL1. cbn [Z.b2z] in FL1.
    cstep. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    cstep. cstep. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    fold uh. change 18446744073709551616 with (2 ^ 64). fold p1. fold La1.
    cstep. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    subst La0 La1. rewrite <- D0, <- D1 in *.
    eapply evtA_mono.
    2:{ intros ms' Q. exists p1. split; [right; reflexivity|]. split; [exact (LM01 eq_refl)| exact Q]. }
    lazymatch goal with MUx : munch _ m ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (MUw : munch (sm1_W sp fsbase p1) m mx) by (eapply munch_weaken; [| exact MUx]; unfold sub_fp, sm1_W; cbn; intros xx Hxx; tauto) end.
    eapply (sm1_tail ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ _ _ F fc m _ lo fsbase p1 SB);
      [ exact P1 | exact LOC' | lia | lia | exact G1 | exact G2 | exact G3' | exact G4' | exact ESB
      | eassumption | exact IG | exact MUw | eassumption | eassumption | eassumption | eassumption
      | eassumption | eassumption | eassumption
      | exact PSTK | exact PIMG | exact PFS | exact PFSH ].
  - (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    cstep. (* [comment removed for export] *)
    subst La0 La1. rewrite <- D0, <- D1 in *.
    eapply evtA_mono.
    2:{ intros ms' Q. exists p0. split; [left; reflexivity|]. split; [exact LM0| exact Q]. }
    lazymatch goal with MUx : munch _ m ?mx |- evtA _ _ _ (MS _ _ _ _ _ ?mx _) =>
      assert (MUw : munch (sm1_W sp fsbase p0) m mx) by (eapply munch_weaken; [| exact MUx]; unfold sub_fp, sm1_W; cbn; intros xx Hxx; tauto) end.
    eapply (sm1_tail ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 _ _ _ _ F fc m _ lo fsbase p0 SB);
      [ exact P0 | exact LOC' | lia | lia | exact G1 | exact G2 | exact G3' | exact G4' | exact ESB
      | eassumption | exact IG | exact MUw | eassumption | eassumption | eassumption | eassumption
      | eassumption | eassumption | eassumption
      | exact PSTK | exact PIMG | exact PFS | exact PFSH ].
  all: lazymatch goal with |- ?g => idtac "MAINGOAL" g end.
Qed.
End SMW.
End RC__1.
