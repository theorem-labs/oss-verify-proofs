(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_CombinedMiss AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AllocWalkKit.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_AllocPre AW_MallocPre AW_FreeLeaves AW_IAInit AW_FreePre AW_ReallocPre AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Definition realloc_head_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo size needed rz c CA P TSD CTX TH sb TOP BOT : Z) (T : list Z) (d : depot) (mc : word) (P0 : Z) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 cfu : word) (jk j8 jr1 jr2 : list byte) (rest : list word) m',
    ms' = MS (mkR (wz 0x19b90c) (Z_to_bv 64 (bv_unsigned sp + -2384)) gp tp t0 t1 t2 (Z_to_bv 64 c) (wz P) (wz CA) (wz P) (wz AINST)
                  (Z_to_bv 64 c) a4 a5 a6 a7 (wz 8) (wz CA) (wz AINST) (wz size) (wz AINST) (wz (bv_unsigned sp + -2136))
                  (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) t3 t4 t5 t6)
             F (Z_to_bv 64 0x19bdac) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030); (TH + 2856, TH + 2872)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ AENV tp TSD CTX TH sb (bv_unsigned sp + -2136) T rest m' /\ length rest = (255 - length T)%nat
    /\ Forall (fun x => 0 <= x < 2^64) T /\ (1 <= length T <= 30)%nat
    /\ stk asegs m' lo (bv_unsigned sp + -2384)
    /\ rw_cells asegs m' (bv_unsigned sp + -2384) [C8 (wz rz); C8 (wz needed); C8 (wz 8); C8 (wz size); C8 (wz 1); C8 (wz 0x19709c)]
    /\ aframe (Z_to_bv 64 (bv_unsigned sp + -2208)) (wz 0x19797c) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz P0) (wz AINST) (wz size)
              cfu (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 m' j8
    /\ rw_cells asegs m' (bv_unsigned sp + -2208) [C8 cfu; C8 (wz 0x1bf8f0); C8 (wz P0); C8 (wz size); C8 sp; C8 (wz 0x197900)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2160) [CB 8 jr1; C8 (wz 0x1bf960)]
    /\ rw_cells asegs m' (bv_unsigned sp + -2144) [CB 8 jr2]
    /\ rw_cells asegs m' (bv_unsigned sp + -80) [C8 sp]
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [CB 8 jk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' P [C4 (wz 0); C4 mc]
    /\ rw_cells asegs m' (TH + 3168) [C1 (b8 0)]
    /\ DEPOT asegs d m'
    /\ rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)] /\ ia_after m'
    /\ stk asegs m' (TH + 2800) (TH + 3168).
End HCW.

Section HeadR.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)).
  Variables (sb : Z) (mc : word) (P0 : Z) (inited : bool).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x1bf8f0 (bv_unsigned sp) TOP BOT 30 CHI.
  Variables (rz needed c CA P : Z).
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz /\ c = class_id needed /\ CA = TH + 208 /\ P = CA + 80 * c).
  Let W : list ivl := [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030); (TH + 2856, TH + 2872)].
  Let POST := realloc_head_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo size needed rz c CA P TSD CTX TH sb TOP BOT T d mc P0.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2592 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  Hypothesis PLCD : hidden ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Let PLACED : Prop := ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX))
               /\ ((TH + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= TH) /\ (TH + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= TH)
                /\ (sb + kSpaceSize + 4096 <= d_nb d \/ d_nb d + 16 * 65536 <= sb) /\ (sb + kSpaceSize + 4096 <= d_sb d \/ d_sb d + 8 * 131072 <= sb)
                /\ (CTX + 160 <= d_nb d \/ d_nb d + 16 * 65536 <= CTX) /\ (CTX + 160 <= d_sb d \/ d_sb d + 8 * 131072 <= CTX)
                /\ aapp (d_nb d) (16 * 65536) /\ aapp (d_sb d) (8 * 131072)).
  Hypothesis SBR : hidden (AHI_LO <= sb /\ sb + kSpaceSize <= aceil /\ sb mod 65536 = 0).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz P0.
  Hypothesis Ha1 : a1 = wz size.
  Hypothesis P0R : AIMG_TOP + 16 <= P0 /\ P0 < aceil.
  Hypothesis SZ64 : size <= 64512.
  (* [comment removed for export] *)
  Hypothesis FLG : rw_cells asegs m AIAINIT [C1 (b8 (if inited then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Hypothesis IA : if inited then ia_after m else ia_pristine m.

  Ltac prepH :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCA & DP)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 4096 <= TOP /\ TOP <= 140737488355328 /\ 0 <= BOT /\ BOT < TOP)
      by (clear - LO RNG SBR TPR SPT TBR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct TPR as [TPR'];
          destruct SPT as [SPT']; destruct TBR as [TBR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SPT', TBR'; lia);
        region_sides; name_bands;
    assert (HC : 1 <= c < 32)
      by (clear - SZ DC DNEED DRZ; try acb; subst c needed rz; apply class_id_range; unfold kMaxSize in SZ; pose proof (rz_size_facts size); unfold round_up in *;
          Z.div_mod_to_equations; lia);
    assert (RZB : 16 <= rz <= 2048 /\ size + rz <= needed /\ 8 + rz <= needed /\ needed < size + rz + 8)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : P = TH + 208 + 80 * c /\ CA = TH + 208) by (rewrite DP, DCA; split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz)) by (constructor; repeat split; assumption);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    clear DRZ DNEED DC DCA DP.
  Ltac plia :=
    first [ lia
          | match goal with H : hidden PLACED |- _ =>
              let P := fresh "PLu" in pose proof H as P; destruct P as [P]; unfold PLACED, kSpaceSize, AHI_LO in P;
              let A1 := fresh "PA" in let A2 := fresh "PA" in let A3 := fresh "PA" in
              let B1 := fresh "PB" in let B2 := fresh "PB" in let B3 := fresh "PB" in let B4 := fresh "PB" in
              let B5 := fresh "PB" in let B6 := fresh "PB" in let B7 := fresh "PB" in let B8 := fresh "PB" in
              destruct P as [[A1 [A2 A3]] [B1 [B2 [B3 [B4 [B5 [B6 [B7 B8]]]]]]]];
              first [ clear A2 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A3 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 B1 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B2 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B3 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B4 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B5 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B6; lia
                    | clear A1 A2 A3 B1 B2 B3 B4 B5; lia ]
            end ].
  Ltac solve_depot_avoid ::=
    unfold depot_avoid, avoids; rewrite ?d_nb_put, ?d_sb_put; cbn [fst snd];
    repeat split;
    repeat (first [apply Forall_nil | apply Forall_cons; [cbn beta iota delta [fst snd]; plia |]]).
  (* [comment removed for export] *)
  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => lia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => lia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  Theorem realloc_head :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m P [C4 (wz 0); C4 mc] ->
    rw_cells asegs m (TH + 3168) [C1 (b8 0)] ->
    stk asegs m (TH + 2800) (TH + 3168) ->
    DEPOT asegs d m ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bf7b4) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST QC1 UNW TST DEP.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold W in MU. prepH. unfold wz in *. unfold AINST.
    (* [comment removed for export] *)
    rewrite Ha0.
    eapply evt_cut.
    { eapply (@realloc_pre _ ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 P0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo size d inited TSD CTX TH TOP BOT CH sb);
        try eassumption.
      - rewrite unsigned_lit by (clear - P0R; unfold AIMG_TOP in P0R; try acb; lia). clear - P0R; try acb; lia.
      - rewrite unsigned_lit by (clear - P0R; unfold AIMG_TOP in P0R; try acb; lia). clear - P0R; unfold AIMG_TOP in P0R; lia.
      - clear - SZ SZ64; try acb; lia. }
    cbv beta. intros ms1 PO1.
    destruct PO1 as (x3 & x4 & x5 & x12 & x13 & x14 & x15 & x16 & x17 & cfu & jk & jr1 & jr2 & rest & m1 & -> & MU1 & WM1 & MI1 & ENV1 & ST1 & FRR1 & FRA1 & FP1 & ESO1 & TRB1 & LR1 & TFB1 & F81
                     & UNW1 & TST1 & DEP1 & TRNG & NR & FLG1 & IA1).
    repeat match goal with H : context [utrace 0x1bf8f0 _ _ _ _ _] |- _ => progress (fold CHI in H; fold T in H) end.
    unfold AIAINIT, AIAINST in MU1. unfold AIAINIT in FLG1.
    (* [comment removed for export] *)
    eapply rw_cells_transport in QC1; [| exact MU1| exact WM1| cbn [disjoint_from cells_size csize length Nat.add Nat.mul];
      match goal with TB : akobj TH 4096 |- _ => clear - BND PB HI TB end; try acb; aunf; lia].
    clear MU WM MI ST UNW TST DEP ENV. rename MI1 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp + -2208)] m1) as MU. pose proof (wmono_refl asegs m1) as WM.
    lazymatch goal with H : IENV _ _ _ _ _ _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into ENV1 end.
    pose proof ENV1 as E. open_ienv E.
    lazymatch goal with H : u64arr asegs ?mm (bv_unsigned sp + -2136 + 16) (map wz T ++ ?rest) |- _ =>
      assert (AE : AENV tp TSD CTX TH sb (bv_unsigned sp + -2136) T rest mm)
        by (econstructor; try eassumption; replace (bv_unsigned sp + -2136 + 16) with (bv_unsigned sp + -2136 + 16) by lia; eassumption) end.
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Emcs Epsc Ecfu Estk Et40.
    (* [comment removed for export] *)
    lazymatch goal with H : AENV tp TSD CTX TH sb _ T ?rest ?mm |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      callD (@allocate_pre _ (Z_to_bv 64 0x19797c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp _ _ _ (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 P0) (Z_to_bv 64 AINST)
               (Z_to_bv 64 size) (Z_to_bv 64 8) (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 1) (Z_to_bv 64 1) _ _
               (Z_to_bv 64 AINST) (Z_to_bv 64 size) _ (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11 _ _ _ _
               F fc mm lo size (bv_unsigned sp + -2136) T rest d TSD CTX TH sb 1 [0] rz needed c (class_size c) (class_size c / 8)
               (Z.min size 4096) CA P 0 (sb + c * 2^32) (sb + c * 2^32 + rz) (Z.of_nat (length T)) (d_putid d (depot_hash T))) end.
    all: rewrite ?unsigned_lit by lia.
    { constructor. destruct DEFS as [D]. clear - D; try acb. cbn [hd]. repeat split; try lia; tauto. }
    { exact LO. }
    { clear - HI; try acb; lia. }
    { constructor. clear - SPQ; try acb; rewrite SPQ; Z.div_mod_to_equations; lia. }
    { exact SZ. }
    { exact TPR. }
    { exact RNG. }
    { exact PLC. }
    { exact PLCD. }
    { exact SBR. }
    { reflexivity. }
    { clear; lia. }
    { constructor. clear - HC BND; try acb. pose proof (class_size_table_facts c ltac:(hci; clear - HC; try acb; lia)). unfold kSpaceSize. nia. }
    { constructor. destruct SPT as [SPT']. clear - SPT'; try acb. lia. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { exact AE. }
    { assumption. }
    { assumption. }
    replace (bv_unsigned sp + -2208 + -128) with (bv_unsigned sp + -2336) in * by lia.
    clear AE ENV1.
    (* [comment removed for export] *)
    lazymatch goal with H : AENV tp TSD CTX TH sb _ T _ ?mm, H2 : aframe _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      open_env H; unfold aframe in H2; rewrite unsigned_lit in H2 by lia end.
    replace (bv_unsigned sp + -2208 + -128) with (bv_unsigned sp + -2336) in * by lia.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      callD (combined_head (Z_to_bv 64 0x19709c) (Z_to_bv 64 (bv_unsigned sp + -2336)) gp tp _ _ _ (Z_to_bv 64 1) (Z_to_bv 64 size)
               (Z_to_bv 64 AINST) (Z_to_bv 64 (TH + 208)) (Z_to_bv 64 needed) (Z_to_bv 64 8) _ _ _ _
               (Z_to_bv 64 8) (Z_to_bv 64 needed) (Z_to_bv 64 rz) (Z_to_bv 64 size) (Z_to_bv 64 AINST) (Z_to_bv 64 (bv_unsigned sp + -2136))
               (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 TH) (Z_to_bv 64 1) _ _ _ _ F fc mm lo needed (TH + 208)) end.
    all: rewrite ?unsigned_lit by lia.
    (* [comment removed for export] *)
    all: try (match goal with TB : akobj TH 4096 |- akobj _ _ /\ _ =>
                destruct RNG as [(_ & _ & _ & _ & _ & _ & T16)]; clear - BND TB T16;
                split; [eapply akobj_sub; [exact TB| lia| lia] | split; [lia| Z.div_mod_to_equations; lia]] end).
    { assumption. }
    { assumption. }
    { clear - HI; try acb; lia. }
    { reflexivity. } { reflexivity. } { reflexivity. } { reflexivity. }
    { clear - SZ RZB; try acb; lia. }
    replace (bv_unsigned sp + -2336 + -48) with (bv_unsigned sp + -2384) in * by lia.
    (* [comment removed for export] *)
    unhide_hyp EQh. destruct EQh as (Ec & Erz & Eneeded). destruct EQS as (EP & ECA). rewrite <- Ec.
    lazymatch goal with H : rw_cells asegs ?mm P [C4 _; C4 mc] |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      replace P with (TH + 208 + PCLASS_SIZE * c) in H by (unfold PCLASS_SIZE; clear - EP; try acb; lia);
      eapply evt_cut; [ eapply combined_to_refill; [exact HC | exact H] |] end.
    cbv beta. intros ms' ->.
    replace (TH + 208 + PCLASS_SIZE * c) with P in * by (unfold PCLASS_SIZE; clear - EP; try acb; lia). rewrite <- ECA.
    apply evt_done. unfold POST, realloc_head_post, wz, AINST.
    lazymatch goal with H : rw_cells asegs ?mm (bv_unsigned sp + -72) (CB 8 ?jk :: _), H2 : rw_cells asegs _ (bv_unsigned sp + -2336) (CB 8 ?j8 :: _),
                         H3 : u64arr asegs _ _ (map _ T ++ ?rest), H4 : rw_cells asegs _ (bv_unsigned sp + -2208) (C8 ?cfu :: _),
                         H5 : rw_cells asegs _ (bv_unsigned sp + -2160) (CB 8 ?jr1 :: _), H6 : rw_cells asegs _ (bv_unsigned sp + -2144) [CB 8 ?jr2] |- _ =>
      do 11 eexists; exists cfu, jk, j8, jr1, jr2, rest, mm end.
    split; [reflexivity|].
    split. { first [exact MU1 | eapply munch_trans; [exact MU1|]; eapply munch_weaken; [| exact MU]; intros x Hx; cbn [outside] in Hx |- *; destruct Hx as [Hx _]; split; [clear - Hx; lia| exact I]]. }
    split; [first [exact WM1 | eapply wmono_trans; [exact WM1| exact WM]]|]. split; [assumption|].
    split; [econstructor; eassumption|].
    lazymatch goal with |- context [ia_after ?mm] =>
      first [ lazymatch type of FLG1 with rw_cells _ mm _ _ => idtac end
            | eapply rw_cells_transport in FLG1; [| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; clear - BND HI; try acb; lia] ] end.
    lazymatch goal with |- context [ia_after ?mm] =>
      pose proof (ia_if_transport true _ _ mm IA1 MU WM ltac:(hci; cbn [disjoint_from]; clear - BND HI; try acb; lia)) as IA2 end.
    lazymatch goal with |- context [ia_after ?mm] =>
      first [ lazymatch type of TST1 with stk _ mm _ _ => idtac end
            | eapply stk_transport_disjoint in TST1; [| exact MU| exact WM| cbn [disjoint_from]; clear - BND HI; try acb; lia] ] end.
    repeat match goal with |- _ /\ _ => split end; try assumption.
    all: try (clear - NR; lia).
    all: try (clear - PC10 POST0; try acb; lia).
    all: try exact IA2.
    unfold aframe. rewrite unsigned_lit by lia. replace (bv_unsigned sp + -2208 + -128) with (bv_unsigned sp + -2336) by lia. assumption.
  Qed.
End HeadR.

