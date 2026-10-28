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
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_AllocPre AW_AllocPost AW_MallocRet AllocTacX.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section HCW.
  Context {HCEIL : HeapCeil}.

Local Unset Keyed Unification.

(* [comment removed for export] *)
Lemma combined_miss_backP : forall (fra sp gp tp t0 t1 t2 fs0 fs1 fs2 fs3 fs4 a1 a2 a3 a4 a5 a6 a7 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo c CA sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word) (P : Z),
  P = CA + 80 * c ->
  mem_inv asegs m -> stk asegs m lo (bv_unsigned sp + -48) -> aceil <= lo -> lo + 48 <= bv_unsigned sp -> bv_unsigned sp mod 16 = 0 ->
  rw_cells asegs m (bv_unsigned sp + -48) [C8 fs4; C8 fs3; C8 fs2; C8 fs1; C8 fs0; C8 fra] ->
  1 <= c < 32 -> akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0 -> 0 <= sb /\ sb + kSpaceSize <= aceil ->   (* [comment removed for export] *)
  rw_cells asegs m (AINST + 32) [C8 (wz sb)] ->
  rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs m (P + 8) [C8 (wz (class_size c))] ->
  u32arr asegs m (P + 16) (wlist (rev chunks)) -> cnt = zlen chunks -> 1 <= cnt <= 16 ->
  stk asegs m (P + 16 + 4 * cnt) (P + 80) -> Forall (fun cp => 0 <= cp < 2^32) chunks ->
  rw_cells asegs m (CA + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
  evt asegs (combined_hit_post fra sp gp tp fs0 fs1 fs2 fs3 fs4 s5 s6 s7 s8 s9 s10 s11 F fc m lo P CA c sb cnt mc chunks)
    (MS (mkR (wz 0x19b90c) (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 (Z_to_bv 64 c) (Z_to_bv 64 P) (wz 1) a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 8) (Z_to_bv 64 CA) (Z_to_bv 64 AINST) s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19b90c) fc None m (seg_rom asegs)).
Proof.
  intros until P. intros EP. intros.
  replace P with (CA + PCLASS_SIZE * c) in * by (unfold PCLASS_SIZE; lia).
  eapply combined_miss_back; try eassumption. apply munch_refl. apply wmono_refl.
Qed.
End HCW.

Section Tail.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (T : list Z) (rest : list word).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  Let SO := bv_unsigned sp + -2136.
  (* [comment removed for export] *)
  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z) (P0 : Z) (cfu : word).
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, bv_unsigned sp + -2208) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: depot_W d.
  Let W2 : list ivl := (lo, bv_unsigned sp + -2208) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: nil.
  Let POST := allocate_post (Z_to_bv 64 0x19797c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz P0) (wz AINST) (wz size)
                            cfu (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11
                            F fc m W lo size AB U rz csz P cnt mc TH id chunks (d_put d (depot_hash T) n).
  Let AFR := aframe (Z_to_bv 64 (bv_unsigned sp + -2208)) (wz 0x19797c) (Z_to_bv 64 (bv_unsigned sp + -2136)) (wz P0) (wz AINST) (wz size)
                    cfu (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2560 <= bv_unsigned sp.
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
  Hypothesis CNT : cnt = zlen chunks. Hypothesis HIT : 1 <= cnt <= 16.
  Hypothesis CPS : Forall (fun cp => 0 <= cp < 2^32) chunks.
  Hypothesis ABR : hidden (sb <= AB /\ AB + csz <= sb + kSpaceSize).
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + 31 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  (* [comment removed for export] *)
  Hypothesis NRT : (1 <= length T <= 30)%nat. Hypothesis LR : length rest = (255 - length T)%nat. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.

  Ltac prepI :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 4096 <= TOP /\ TOP <= 140737488355328 /\ 0 <= BOT /\ BOT < TOP)
      by (clear - LO RNG SBR ABR TPR SPT TBR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct ABR as [ABR']; destruct TPR as [TPR'];
          destruct SPT as [SPT']; destruct TBR as [TBR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SPT', TBR'; lia);
        region_sides; name_bands;
    assert (HC : 1 <= c < 32)
      by (clear - SZ DC DNEED DRZ; try acb; subst c needed rz; apply class_id_range; unfold kMaxSize in SZ; pose proof (rz_size_facts size); unfold round_up in *;
          Z.div_mod_to_equations; lia);
    assert (CSZ : 32 <= csz <= 65536 /\ needed <= csz)
      by (clear - SZ HC DCSZ DNEED DRZ DC; try acb; pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz;
          pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; subst needed rz; pose proof (rz_size_facts size); unfold round_up in *;
                                             Z.div_mod_to_equations; lia)); subst c; lia);
    assert (RZB : 16 <= rz <= 2048 /\ size + rz <= needed /\ 8 + rz <= needed /\ needed < size + rz + 8)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (ALN : exists thq sbq rzk ck nk, TH = 16 * thq /\ sb = 65536 * sbq /\ rz = 16 * rzk /\ csz = 32 * ck /\ needed - rz = 8 * nk)
      by (clear - RNG SBR HC DCSZ DNEED DRZ; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; pose proof (rz_size_facts size);
          pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz needed rz; unfold round_up;
          exists (TH / 16), (sb / 65536), (rz_size size / 16), (class_size c / 32), ((size `max` 8 + 8 - 1) / 8);
          Z.div_mod_to_equations; lia);
    destruct ALN as (thq & sbq & rzk & ck & nk & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : U = AB + rz /\ P = TH + 208 + 80 * c /\ AB = sb + c * 2 ^ 32 + cp * 16 /\ n = Z.of_nat (length T) /\ CA = TH + 208)
      by (rewrite DU, DP, DAB, DN, DCA; repeat split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ csz = class_size c /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz
                       /\ cp = hd 0 chunks /\ id = d_putid d (depot_hash T) /\ csz8 = csz / 8)) by (constructor; repeat split; first [assumption | reflexivity]);
    assert (C8F : 8 * csz8 = csz) by (clear - ALN DC8; try acb; subst csz8; Z.div_mod_to_equations; lia);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    assert (SHR : 2201439137792 <= sh AB /\ sh AB + csz8 <= 17594333495296) by (clear - BND C8F; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    assert (NR : 1 <= n <= 30) by (rewrite DN; clear - NRT; try acb; lia);
    clear DRZ DNEED DC DCSZ DC8 DFL DCA DP DCP DAB DU DN DID.

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

  Theorem realloc_from_refill : forall (x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (j8 : list byte),
    AENV tp TSD CTX TH sb SO T rest m -> mem_inv asegs m ->
    stk asegs m lo (bv_unsigned sp + -2384) ->
    (* [comment removed for export] *)
    rw_cells asegs m (bv_unsigned sp + -2384) [C8 (wz rz); C8 (wz needed); C8 (wz 8); C8 (wz size); C8 (wz 1); C8 (wz 0x19709c)] ->
    AFR m j8 ->
    (* [comment removed for export] *)
    rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs m (P + 8) [C8 (wz csz)] -> u32arr asegs m (P + 16) (wlist (rev chunks)) ->
    stk asegs m (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs m (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs m AB (AB + csz) ->
    u8arr asegs m (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs m (TH + 2800) (TH + 3168) -> rw_cells asegs m (TH + 3168) [C1 (b8 0)] ->
    DEPOT asegs d m ->
    evt asegs POST
      (MS (mkR (wz 0x19b90c) (Z_to_bv 64 (bv_unsigned sp + -2384)) gp tp x5 x6 x7 (Z_to_bv 64 c) (wz P) (wz 1) x11 x12 x13 x14 x15 x16 x17
               (wz 8) (wz CA) (wz AINST) (wz size) (wz AINST) (wz SO) (Z_to_bv 64 (-8)) (wz 7) (wz TH) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x19b90c) fc None m (seg_rom asegs)).
  Proof.
    intros until j8. intros ENV MI ST FRC FRA QC1 QC2 QC3 QC4 QST CHUNK SHK TST UNW DEP.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    unfold W in MU. prepI. unfold wz in *. unfold AINST.
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (clear - CNT; try acb; unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    destruct EQS as (EU & EP & EAB & En & ECA). open_env ENV.
    unhide_hyp EQh. destruct EQh as (Ec & Ecsz & Erz & Eneeded & Ecp & Eid & E8). rewrite Ecsz in QC2. rewrite <- ECA in QST.
    unfold AFR, aframe in FRA. rewrite unsigned_lit in FRA by lia.
    (* [comment removed for export] *)
    replace (Z_to_bv 64 (bv_unsigned sp + -2384)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2336)) + -48))
      by (f_equal; rewrite unsigned_lit by lia; lia).
    callD (combined_miss_backP (Z_to_bv 64 0x19709c) (Z_to_bv 64 (bv_unsigned sp + -2336)) gp tp x5 x6 x7
             (Z_to_bv 64 1) (Z_to_bv 64 size) (Z_to_bv 64 8) (Z_to_bv 64 needed) (Z_to_bv 64 rz) x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 size) (Z_to_bv 64 6976152) (Z_to_bv 64 SO) (Z_to_bv 64 (-8)) (Z_to_bv 64 7) (Z_to_bv 64 TH) (Z_to_bv 64 1) x28 x29 x30 x31
             F fc m lo c CA sb cnt mc chunks j0 j1 j2 j3 P).
    all: rewrite ?unsigned_lit by (first [clear - BND HI; lia | lia]).
    all: try replace (bv_unsigned sp + -2336 + -48) with (bv_unsigned sp + -2384) by (first [clear; lia | lia]).
    { clear - EP ECA; try acb; lia. }
    { exact MI. }
    { exact ST. }
    { exact LO. }
    { clear - HI; try acb; lia. }
    { clear - SPQ; try acb; rewrite SPQ; Z.div_mod_to_equations; lia. }
    { exact FRC. }
    { exact HC. }
    { match goal with TB : akobj TH 4096 |- _ => clear - BND ALN ECA TB end; try acb; subst CA;
      split; [eapply akobj_sub; [eassumption| lia| lia] | split; [lia| Z.div_mod_to_equations; lia]]. }
    { clear - BND; try acb; acb; unfold kSpaceSize; lia. }
    { exact Einst1. }
    { exact QC1. }
    { exact QC2. }
    { exact QC3. }
    { exact CNT. }
    { exact HIT. }
    { exact QC4. }
    { exact CPS. }
    { exact QST. }
    clear ST.
    (* [comment removed for export] *)
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      assert (AE : AENV tp TSD CTX TH sb SO T rest mm) by (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]) end.
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2.
    replace (Z_to_bv 64 (bv_unsigned sp + -2336)) with (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -2208)) + -128))
      by (f_equal; rewrite unsigned_lit by lia; lia).
    rewrite <- Ecp, <- EAB.
    unfold depot_W in MU.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (@partC_post _ (Z_to_bv 64 0x19797c) (Z_to_bv 64 (bv_unsigned sp + -2208)) gp tp (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 P0)
           (Z_to_bv 64 AINST) (Z_to_bv 64 size) cfu (Z_to_bv 64 (bv_unsigned sp + -2136)) (Z_to_bv 64 (bv_unsigned sp + -89)) s7 s8 s9 s10 s11
           F fc mm lo size SO T rest d TSD CTX TH sb cnt mc chunks rz needed c csz csz8 fl CA P cp AB U n id) | post_callA segs mm ] end.
    all: rewrite ?unsigned_lit by (first [clear - BND HI; lia | lia]).
    all: try replace (bv_unsigned sp + -2208 + -128) with (bv_unsigned sp + -2336) by (first [clear; lia | lia]).
    all: try exact DEFS. all: try exact AE.
    { exact LO. }
    { clear - HI; try acb; lia. }
    { constructor. clear - SPQ; try acb; rewrite SPQ; Z.div_mod_to_equations; lia. }
    { exact SZ. }
    { exact TPR. }
    { exact RNG. }
    { exact PLC. }
    { exact PLCD. }
    { exact SBR. }
    { exact CNT. }
    { exact HIT. }
    { exact ABR. }
    { constructor. destruct SPT as [SPT']. clear - SPT'; try acb. lia. }
    { clear - NR; try acb; lia. }
    { exact TRNG. }
    { clear - DCAP NR; try acb; lia. }
    { exact DLO. }
    { assumption. }
    { apply munch_refl. }
    { apply wmono_refl. }
    { unfold aframe. rewrite unsigned_lit by lia. exact FRA. }
    { assumption. }
    { assumption. }
    { assumption. }
    { assumption. }
    { lazymatch goal with H : rw_cells asegs _ (CA + CACHE_STATS) _ |- _ => unfold CACHE_STATS in H; rewrite ECA in H; exact H end. }
    { exact CHUNK. }
    { exact SHK. }
    { exact TST. }
    { exact DEP. }
    (* [comment removed for export] *)
    apply evt_done. unfold POST, allocate_post. rewrite (ret_pc_even 0x19797c) by (clear; lia). unfold wz, AINST. rewrite ?unsigned_lit by (first [clear - BND HI; lia | lia]).
    do 14 eexists.
    lazymatch goal with H : rw_cells asegs _ (TH + 208 + 2560) [C8 ?a; C8 ?b; C8 ?c0; C8 ?d0], H1 : b1_ok ?e |- _ => exists a, b, c0, d0, e end.
    eexists. split; [reflexivity|].
    split. 2: split. 3: repeat match goal with |- _ /\ _ => split end; try assumption.
    - unfold W, depot_W. exact MU.
    - exact WM.
  Qed.
End Tail.

