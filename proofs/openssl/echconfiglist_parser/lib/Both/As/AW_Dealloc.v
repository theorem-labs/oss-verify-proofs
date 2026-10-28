(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib Require Import AsanAllocModel.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import ASegs AsShadow AllocWf AllocKit AllocRep AsAtomics F_memset
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_FreeLeaves AW_IAInit AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocPerfKit AllocPerfKit3.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition dealloc_post (sp gp tp s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo U size b1 actx TH : Z) (T : list Z) (d : depot) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a6 a7 t3 t4 t5 t6 : word) m',
    ms' = MS (mkR (wz 0x1bf32c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp t0 t1 t2 sp (wz U)
                  (wz (AINST + OI_Q)) (wz (TH + OT_TQ)) (wz (TH + OT_CACHE)) (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz (U + -16)) (wz size) a6 a7
                  (wz 0x1bf2bc) (wz 1) (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 0x19b2c8) fc None m' (seg_rom asegs)
    /\ munch ([(lo, bv_unsigned sp + -2128); (U + -16, U + -12); (U, U + 8); (TH + 2800, TH + 3168)] ++ depot_W d) m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)]
    /\ rw_cells asegs m' U [C8 (wz (d_putid d (depot_hash T)))]
    /\ stk asegs m' (TH + 2800) (TH + 3168)
    /\ DEPOT asegs (d_put d (depot_hash T) (Z.of_nat (length T))) m'.
End HCW.

Section Dealloc.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (sp gp tp x3 x4 x5 x12 x13 x14 x15 x16 x17 s6 s7 s8 s9 s10 s11 a0 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo U size b1 actx : Z) (ub : list byte) (T : list Z) (rest : list word) (d : depot).
  Variables (TSD CTX TH TOP BOT sb : Z).
  Let W : list ivl := [(lo, bv_unsigned sp + -2128); (U + -16, U + -12); (U, U + 8); (TH + 2800, TH + 3168)] ++ depot_W d.
  Let W2 : list ivl := [(lo, bv_unsigned sp + -2128); (U + -16, U + -12); (U, U + 8); (TH + 2800, TH + 3168)].
  Let POST := dealloc_post sp gp tp s6 s7 s8 s9 s10 s11 F fc m lo U size b1 actx TH T d.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis Ha0 : a0 = wz U.
  Hypothesis UR : hidden (aapp U 8 /\ AIMG_TOP + 16 <= U /\ U + 8 <= aceil /\ U mod 16 = 0).   (* [comment removed for export] *)
  Hypothesis SZ : 1 <= size < 2^32.
  Hypothesis B1 : 0 <= b1 < 256 /\ (b1 mod 128 = 17 \/ b1 mod 128 = 65).
  Hypothesis ACR : 0 <= actx < 2^64.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLU : hidden ((TH + 4096 <= U - 16 \/ U + 8 <= TH) /\ (CTX + 160 <= U - 16 \/ U + 8 <= CTX)
                /\ (d_nb d + 16 * 65536 <= U - 16 \/ U + 8 <= d_nb d) /\ (d_sb d + 8 * 131072 <= U - 16 \/ U + 8 <= d_sb d)).
  Hypothesis PLC : hidden (CTX + 160 <= TH \/ TH + 4096 <= CTX).
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Let PLACED : Prop := ((TH + 4096 <= U - 16 \/ U + 8 <= TH) /\ (CTX + 160 <= U - 16 \/ U + 8 <= CTX)
                /\ (d_nb d + 16 * 65536 <= U - 16 \/ U + 8 <= d_nb d) /\ (d_sb d + 8 * 131072 <= U - 16 \/ U + 8 <= d_sb d))
               /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)
               /\ ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis NR : (1 <= length T <= 30)%nat. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis LREST : length rest = (255 - length T)%nat.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + Z.of_nat (length T) + 1 <= 131072.

  Ltac prepD :=
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 4096 <= TOP /\ TOP <= 140737488355328 /\ 0 <= BOT /\ BOT < TOP
               /\ 12599312 <= U /\ U + 8 <= aceil /\ 12599296 <= d_nb d /\ 12599296 <= d_sb d /\ 140735193776128 <= aceil)
      by (clear - LO RNG TPR SPT TBR UR PLCD; try acb; destruct RNG as [RNG']; destruct TPR as [TPR']; destruct UR as [UR']; destruct PLCD as [PLCD'];
          destruct SPT as [SPT']; destruct TBR as [TBR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SPT', TBR'; lia);
        region_sides; name_bands;
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (UQ : exists uq, U = 16 * uq) by (clear - UR; try acb; destruct UR as [UR']; exists (U / 16); Z.div_mod_to_equations; lia);
    destruct UQ as [uq UQ];
    assert (PLCh : hidden PLACED) by (destruct PLU as [PLU']; destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLU' (conj PLC' PLCD')))).

  Ltac plia :=
    first [ lia
          | match goal with H : hidden PLACED |- _ =>
              let P := fresh "PLu" in pose proof H as P; destruct P as [P]; unfold PLACED, AHI_LO in P;
              let A1 := fresh "PA" in let A2 := fresh "PA" in let A3 := fresh "PA" in let A4 := fresh "PA" in let A5 := fresh "PA" in
              let B1 := fresh "PB" in let B2 := fresh "PB" in let B3 := fresh "PB" in let B4 := fresh "PB" in
              let B5 := fresh "PB" in let B6 := fresh "PB" in
              destruct P as [[A1 [A2 [A3 A4]]] [A5 [B1 [B2 [B3 [B4 [B5 B6]]]]]]];
              first [ clear A2 A3 A4 A5 B1 B2 B3 B4; lia
                    | clear A1 A3 A4 A5 B1 B2 B3 B4; lia
                    | clear A1 A2 A4 A5 B1 B2 B3 B4; lia
                    | clear A1 A2 A3 A5 B1 B2 B3 B4; lia
                    | clear A1 A2 A3 A4 B1 B2 B3 B4; lia
                    | clear A1 A2 A3 A4 A5 B2 B3 B4; lia
                    | clear A1 A2 A3 A4 A5 B1 B3 B4; lia
                    | clear A1 A2 A3 A4 A5 B1 B2 B4; lia
                    | clear A1 A2 A3 A4 A5 B1 B2 B3; lia ]
            end ].
  Ltac solve_depot_avoid ::=
    unfold depot_avoid, avoids; rewrite ?d_nb_put, ?d_sb_put; cbn [fst snd];
    repeat split;
    repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; plia |]]).
  (* [comment removed for export] *)
  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => plia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => plia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  Lemma ienv_now_d : forall m1, IENV tp TSD CTX TH sb TOP BOT m -> munch W m m1 -> wmono asegs m m1 -> IENV tp TSD CTX TH sb TOP BOT m1.
  Proof.
    intros m1 E MU WM. unfold W, depot_W in MU. cbn [app] in MU.
    clear SZ ACR.   (* [comment removed for export] *)
    prepD.
    (* [comment removed for export] *)
    pose proof B1 as DEPB1; pose proof NR as DEPNR; pose proof LREST as DEPLR.
    (* [comment removed for export] *)
    apply (ienv_transport_split tp TSD CTX TH sb TOP BOT m m1 _
             [(lo, bv_unsigned sp + -2128); (U + -16, U + -12); (U, U + 8); (TH + 2800, TH + 3168); (d_nb d, d_nb d + 16 * 65536); (d_sb d, d_sb d + 8 * 131072)]
             [(7915480, 12109800 + 8); (7849928, 7849928 + 28)] E MU WM).
    28-32: (cbn [disjoint_from]; let A := fresh in let B := fresh in let C := fresh in let D := fresh in
         pose proof PLU as A; pose proof PLC as B; pose proof PLCD as C; pose proof THB as D; destruct A as [A]; destruct B as [B]; destruct C as [C];
         unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO, AHI_LO, AIMG_TOP in D; clear - BND HI SPR DLO A B C D;
         destruct C as (C1 & C2 & C3 & C4 & _); repeat split; (first [clear - BND H H0 C3 C4 H2 C1 C2; lia | lia])).
    1: (clear; intros a n Ho Hi; cbn [disjoint_from] in *; destruct Ho as (O1 & O2 & O3 & O4 & O5 & O6 & _); destruct Hi as (I1 & I2 & _); repeat split; assumption).
    1: out_img_tac ltac:(cbn [fst snd]; let D := fresh in pose proof THB as D; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO, AHI_LO, AIMG_TOP in D; clear - BND D; lia).
    all: clear - BND; cbn [disjoint_from]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma dealloc_cas : forall (x1 : word) (t0 t1 t2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 t3 t4 t5 t6 xs0 xs1 xs3 xs4 xs5 xs6 : word) m0 (Q : machine_state -> Prop),
    mem_inv asegs m0 ->
    rw_cells asegs m0 (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
    (forall (ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 : word) m1,
        mem_inv asegs m1 -> munch [(U + -16, U + -12)] m0 m1 -> wmono asegs m0 m1 ->
        rw_cells asegs m1 (U + -16) [C1 (b8 3); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
        evt asegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 xs0 xs1 ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7
                          (wz (U + -16)) xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x196bb0) fc None m1 (seg_rom asegs))) ->
    evt asegs Q (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -2192)) gp tp t0 t1 t2 xs0 xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                      (wz (U + -16)) xs3 xs4 xs5 xs6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x196b70) fc None m0 (seg_rom asegs)).
  Proof.
    intros until Q. intros MI HDR KONT. prepD. unfold wz in *.
    pose proof (munch_refl [(U + -16, U + -12)] m0) as MU. pose proof (wmono_refl asegs m0) as WM.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    rewrite (unsigned_lit (U + -16)) by lia.
    replace (Z.land (U + -16) 18446744073709551612) with (U + -16)
      by (change 18446744073709551612 with (2^64 - 2^2); rewrite land_mask_down by lia; clear - UQ; try acb; Z.div_mod_to_equations; lia).
    rewrite (Z.shiftl_mul_pow2 (U + -16) 3) by lia. rewrite (unsigned_lit ((U + -16) * 2^3)) by lia.
    replace (((U + -16) * 2^3) mod 32) with 0 by (clear - UQ; try acb; Z.div_mod_to_equations; lia).
    change (bv_swrap 32 (255 ≪ 0)) with 255. change (bv_swrap 32 (2 ≪ 0)) with 2. change (bv_swrap 32 (3 ≪ 0)) with 3.
    (* [comment removed for export] *)
    assert (B1C : b1 = 17 \/ b1 = 145 \/ b1 = 65 \/ b1 = 193) by (clear - B1; try acb; Z.div_mod_to_equations; lia).
    assert (HW : forall st, 0 <= st < 256 -> cells_bytes [C1 (b8 st); C1 (b8 b1); C2 (Z_to_bv 64 0)] = cells_bytes [C4 (Z_to_bv 64 (st + 256 * b1))]).
    { intros st ST. cbn [cells_bytes cbytes app]. unfold le4, le2, b8. rewrite !unsigned_lit by lia. cbn [Z_to_le_bytes].
      rewrite !Z.shiftr_div_pow2 by lia. cbn [app]. change (2^8) with 256. rewrite (Z.div_small 0 256) by lia.
      assert (E1 : (st + 256 * b1) / 256 = b1) by (clear - ST B1; try acb; Z.div_mod_to_equations; nia).
      rewrite E1. rewrite (Z.div_small b1 256) by lia. rewrite (Z.div_small 0 256) by lia.
      f_equal. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256. clear - ST B1; try acb; Z.div_mod_to_equations; nia. }
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _] [_; _])) in HDR. destruct HDR as [HW0 HREST]. cbn [cells_size csize Nat.add] in HREST.
    apply (rw_cells_reshape _ _ _ [C4 (Z_to_bv 64 (2 + 256 * b1))]) in HW0; [| apply HW; lia| reflexivity| cbn; exact (conj I I)].
    assert (MA : (U + -16) mod 4 = 0) by (clear - UQ; try acb; Z.div_mod_to_equations; lia). assert (MR : 0 <= U + -16 < 2^64) by (clear - BND; try acb; lia).
    Ltac litx := repeat match goal with
      | |- context [Z_to_bv 64 (bv_swrap ?n ?x)] => let v := eval vm_compute in (bv_swrap n x) in change (bv_swrap n x) with v
      | |- context [Z_to_bv 64 (Z.land ?x ?y)] => let v := eval vm_compute in (Z.land x y) in change (Z.land x y) with v
      | |- context [Z_to_bv 64 (Z.lxor ?x ?y)] => let v := eval vm_compute in (Z.lxor x y) in change (Z.lxor x y) with v
      | |- context [Z_to_bv 64 (Z.lor ?x ?y)] => let v := eval vm_compute in (Z.lor x y) in change (Z.lor x y) with v
      | |- context [Z_to_bv 64 (Z.shiftr ?x ?y)] => let v := eval vm_compute in (Z.shiftr x y) in change (Z.shiftr x y) with v
      end.
    Ltac cas_run bb HW HW0 HREST KONT MU :=
      (* [comment removed for export] *)
      astep;
      (* [comment removed for export] *)
      step; litx; step;
      let K := fresh "K" in
      if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]; clear K;
      (* [comment removed for export] *)
      step; step; step; litx;
      astep;
      step; if_cases K; zify_cond K; [exfalso; apply K; reflexivity|]; clear K;
      apply (rw_cells_reshape _ _ _ [C1 (b8 3); C1 (b8 bb); C2 (Z_to_bv 64 0)]) in HW0; [| symmetry; apply (HW 3); lia| reflexivity| cbn; repeat split; exact I];
      lazymatch goal with H : mem_inv asegs _ |- _ => eapply KONT; [exact H| exact MU| assumption|] end;
      apply (proj2 (rw_cells_app asegs _ _ [_; _; _] [_; _])); split; [exact HW0| exact HREST].
    destruct B1C as [-> | [-> | [-> | ->]]]; [cas_run 17 HW HW0 HREST KONT MU | cas_run 145 HW HW0 HREST KONT MU | cas_run 65 HW HW0 HREST KONT MU | cas_run 193 HW HW0 HREST KONT MU].
  Qed.

  Theorem dealloc_seg :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -2128) ->
    rw_cells asegs m (U + -16) [C1 (b8 2); C1 (b8 b1); C2 (wz 0); C4 (wz size); C8 (wz actx)] ->
    rw_cells asegs m U [CB 8 ub] ->
    stk asegs m (TH + 2800) (TH + 3168) ->
    rw_cells asegs m (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))] ->
    u64arr asegs m (bv_unsigned sp + -2128 + 16) (map wz T ++ rest) ->
    DEPOT asegs d m ->
    evt asegs POST
      (MS (mkR (wz 0x1bf32c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x3 x4 x5 sp a0 (wz AINST) a0 (wz 0) (wz 0)
               (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz 1) x12 x13 (wz 0x1bf2bc) (wz 1)
               (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 x14 x15 x16 x17)
          F (Z_to_bv 64 0x196ae8) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST HDR UB TST SOBJ TRB DEP. rewrite Ha0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl W2 m) as MUC. pose proof (wmono_refl asegs m) as WMC.   (* [comment removed for export] *)
    unfold W, depot_W in MU. cbn [app] in MU. unfold W2 in MUC. prepD. unfold AINST, wz in *.
    assert (LENB : length ub = 8%nat) by (destruct UB as [[WF _] _]; cbn in WF; tauto).
    (* [comment removed for export] *)
    step. carve_frame 64%nat ST. spill_frame ltac:(do 8 st1f).   (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    pose proof (i_hooks _ _ _ _ _ _ _ _ (ienv_now_d _ ENV MU WM)) as Ehooks.
    step. callD run_free_hooks_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try lia. all: try (unfold AHOOKS; exact Ehooks).
    step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    rename MI0 into MI. rename POST0 into ST.
    (* [comment removed for export] *)
    eapply dealloc_cas; [exact MI| exact HDR|]. clear HDR.
    intros ya0 ya1 ya2 ya3 ya4 ya5 ya6 ya7 m1 MI1 MU1 WM1 HDR.
    transport_after_call asegs x1 m1 MU1 WM1. clear MU1 WM1 MI. rename MI1 into MI. try clear x1. unfold wz in *|-. unfold wz.
    (* [comment removed for export] *)
    step. step. st1f.
    (* [comment removed for export] *)
    step. step.
    replace (zxb (b8 b1)) with (Z_to_bv 64 b1) by (unfold zxb, b8; f_equal; symmetry; rewrite Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 8) with 256; apply Z.mod_small; lia).
    replace (Z.land (bv_unsigned (Z_to_bv 64 b1)) 3) with 1 by (rewrite unsigned_lit by lia; change 3 with (Z.ones 2); rewrite Z.land_ones; clear - B1; try acb; Z.div_mod_to_equations; lia).
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    step. step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    pose proof (ienv_now_d _ ENV MU WM) as E.
    pose proof (i_tsdi _ _ _ _ _ _ _ _ E) as Etsdi. pose proof (i_tp _ _ _ _ _ _ _ _ E) as Etp.
    pose proof (i_tsd _ _ _ _ _ _ _ _ E) as Etsd. pose proof (i_ctx _ _ _ _ _ _ _ _ E) as Ectx. clear E.
    step. callD getcurthreadstats_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try (first [clear - HI BND; lia | (lia_guard; (lia_guard; lia))]).
    all: try (unfold ATSDINIT; eassumption). all: try (acb; (lia_guard; lia)). all: try (unfold AIMG_TOP; lia).
    clear Etsdi Etp Etsd Ectx.
    lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
    lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI end.
    (* [comment removed for export] *)
    lazymatch goal with H : stk _ _ (TH + 2800) (TH + 3168) |- _ =>
      destruct (stk_split asegs _ (TH + 2800) (TH + 2824) (TH + 3168) H ltac:(hci; lia)) as [TS1 TS2]; clear H;
      destruct (stk_split asegs _ (TH + 2824) (TH + 2840) (TH + 3168) TS2 ltac:(hci; lia)) as [TS3 TS4]; clear TS2 end.
    destruct (stk_cells _ _ _ TS3 ltac:(hci; lia)) as [sj SJ]. clear TS3. replace (TH + 2840 - (TH + 2824)) with 16 in SJ by lia. change (Z.to_nat 16) with 16%nat in SJ.
    apply (rw_cells_split_CB asegs _ _ [] 16 sj [] [8;8]%nat) in SJ; [| reflexivity]. cbn [mk_CB_cells app] in SJ.
    repeat match type of SJ with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in SJ end.
    repeat match goal with H : _ = take _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    unfold wz. step. step. step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    do 14 step.
    release_frame FR ST (bv_unsigned sp + -2128).
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (TST : stk asegs mm (TH + 2800) (TH + 3168)) end.
    { eapply stk_merge; [exact TS1| | lia]. eapply stk_merge; [| exact TS4| lia].
      pose proof (stk_of_rw_cells asegs _ _ _ SJ) as K. cbn [cells_size csize Nat.add] in K.
      replace (TH + 2824 + Z.of_nat 16) with (TH + 2840) in K by lia. exact K. }
    clear TS1 TS4 SJ.
    (* [comment removed for export] *)
    step. carve_frame 48%nat ST. spill_frame ltac:(do 6 st1f). step. step. step.
    step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    (* [comment removed for export] *)
    step. step.
    pose proof (ienv_now_d _ ENV MU WM) as E.
    pose proof (i_tsdi _ _ _ _ _ _ _ _ E) as Etsdi. pose proof (i_tp _ _ _ _ _ _ _ _ E) as Etp.
    pose proof (i_tsd _ _ _ _ _ _ _ _ E) as Etsd. pose proof (i_ctx _ _ _ _ _ _ _ _ E) as Ectx. clear E.
    step. callD getcurthread_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try (first [clear - HI BND; lia | (lia_guard; lia)]).
    all: try (unfold ATSDINIT; eassumption). all: try (acb; (lia_guard; lia)). all: try (unfold AIMG_TOP; lia).
    clear Etsdi Etp Etsd Ectx.
    lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
    lazymatch goal with H : mem_inv asegs _ |- _ => rename H into MI end.
    unfold wz. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    pose proof (ienv_now_d _ ENV MU WM) as E.
    pose proof (i_thr _ _ _ _ _ _ _ _ E) as Ethr. pose proof (i_tid _ _ _ _ _ _ _ _ E) as Etid. clear E. unfold wz in Ethr, Etid.
    step. step. step. step. step. step. clear Ethr Etid.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (DEPOT_transport asegs d _ mm) in DEP; [| exact MUC | exact WMC | solve_depot_avoid] end.
    clear MUC WMC.
    assert (IDR : 1 <= d_putid d (depot_hash T) < 65536) by (apply d_putid_range; [exact (proj1 DEP)| lia]).
    replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) in TRB by lia.
    step. callDep (depot_put_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc lo (bv_unsigned sp + -2112) T rest d).
    all: rewrite ?unsigned_lit by lia. all: try eassumption; try (first [clear - NR HI BND DCAP DLO; lia | lia]).
    all: try (unfold AIMG_TOP; lia).
    rename PC into DEPN. rename MI0 into MI. rename POST0 into ST.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl W2 mm) as MUC; pose proof (wmono_refl asegs mm) as WMC; unfold W2 in MUC end.
    (* [comment removed for export] *)
    step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.lor ?y ?x)] =>
      replace (Z_to_bv 64 (Z.lor y x)) with (Z_to_bv 64 (d_putid d (depot_hash T)));
        [| change y with 0; unfold wz; rewrite (unsigned_lit (d_putid d (depot_hash T))), Z.shiftl_mul_pow2 by (first [clear - NR LREST IDR; lia | lia]);
           rewrite (unsigned_lit (d_putid d (depot_hash T) * 2^32)), Z.shiftr_div_pow2 by lia; rewrite Z.div_mul by lia;
           rewrite unsigned_lit by lia; rewrite Z.lor_0_l; reflexivity] end.
    st1f.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.lor ?y (bv_unsigned (zx32 (Z_to_bv 64 size))))] =>
      replace (Z_to_bv 64 (Z.lor y (bv_unsigned (zx32 (Z_to_bv 64 size))))) with (Z_to_bv 64 size)
        by (change y with 0; rewrite Z.lor_0_l; unfold zx32; rewrite (unsigned_lit size), Z.mod_small, unsigned_lit by lia; reflexivity) end.
    (* [comment removed for export] *)
    do 8 step.
    release_frame FR ST (bv_unsigned sp + -2128).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (DEPOT_transport asegs _ _ mm) in DEPN; [| exact MUC | exact WMC | solve_depot_avoid] end.
    apply evt_done. unfold POST, dealloc_post, wz, AINST, OI_Q, OT_TQ, OT_CACHE. cbn [Z.add].
    do 10 eexists.
    split; [reflexivity|]. split; [unfold depot_W; cbn [app]; exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|].
    split; [exact HDR|]. split; [exact UB|]. split; [exact TST| exact DEPN].
  Qed.
End Dealloc.

