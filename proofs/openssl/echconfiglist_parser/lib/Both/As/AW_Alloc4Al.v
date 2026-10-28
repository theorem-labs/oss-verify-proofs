(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
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
     AsDepotInv AsDepotHash AsDepotPut CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_AllocBase AW_AllocBaseAl AW_Alloc1Al AW_Alloc2Al AW_Alloc3Al AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj. From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import LiaGuard.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.   (* [comment removed for export] *)

Section Alloc.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size SO : Z) (T : list Z) (rest : list word) (d : depot).
  Variables (TSD CTX TH : Z).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  (* [comment removed for export] *)
  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z).
  (* [comment removed for export] *)
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: depot_W d.
  Let W2 : list ivl := (lo, bv_unsigned sp) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3168) :: nil.
  Let POST := allocate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m W lo size AB U rz csz P cnt mc TH id chunks
                            (d_put d (depot_hash T) n).
  Let AFR := aframeAl sp ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 352 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SZ : 1 <= size /\ needed <= kMaxSize.
  (* [comment removed for export] *)
  Hypothesis TPR : hidden (12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= AIMG_TOP).
  Hypothesis RNG : hidden (12109808 <= TSD /\ TSD + 8 <= AIMG_TOP /\ aapp CTX 160 /\ CTX + 160 <= aceil /\ akobj TH 4096 /\ TH + 4096 <= aceil /\ TH mod 16 = 0).
  (* [comment removed for export] *)
  Hypothesis PLC : hidden ((TH + 4096 <= sb \/ sb + kSpaceSize + 4096 <= TH) /\ (CTX + 160 <= sb \/ sb + kSpaceSize + 4096 <= CTX)
                /\ (CTX + 160 <= TH \/ TH + 4096 <= CTX)).
  (* [comment removed for export] *)
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
  Hypothesis ABA : hidden (AB mod 64 = 0).   (* [comment removed for export] *)
  Hypothesis RZ64 : hidden (rz mod 64 = 0).  (* [comment removed for export] *)
  Hypothesis SOR : hidden (bv_unsigned sp <= SO /\ SO + 2064 <= 2^47).
  Hypothesis NR : 1 <= n <= 254. Hypothesis TRNG : Forall (fun x => 0 <= x < 2^64) T.
  Hypothesis DCAP : d_ids d + 1 < 65536 /\ d_frames d + n + 1 <= 131072.
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.


  (* [comment removed for export] *)
  Ltac prep :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 17594333495296 <= sb /\ sb + 137438953472 <= aceil
               /\ sb <= AB /\ AB + csz <= sb + 137438953472 /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp <= SO /\ SO + 2064 <= 140737488355328)
      by (clear - LO RNG SBR ABR TPR SOR; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; destruct ABR as [ABR']; destruct TPR as [TPR'];
          destruct SOR as [SOR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SOR'; lia);
        region_sides; name_bands;
    assert (HC : 1 <= c < 32)
      by (clear - SZ DC DNEED DRZ; try acb; subst c needed rz; apply class_id_range; unfold kMaxSize in SZ; pose proof (rz_size_facts size); unfold round_up in *;
          Z.div_mod_to_equations; lia);
    assert (CSZ : 32 <= csz <= 65536 /\ needed <= csz)
      by (clear - SZ HC DCSZ DNEED DRZ DC; try acb; pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz;
          pose proof (class_size_ge needed ltac:(hci; unfold kMaxSize in SZ; subst needed rz; pose proof (rz_size_facts size); unfold round_up in *;
                                             Z.div_mod_to_equations; lia)); subst c; lia);
    assert (RZB : 16 <= rz <= 2048 /\ size + rz + 64 <= needed /\ 8 + rz <= needed /\ needed < size + rz + 128)
      by (clear - SZ DNEED DRZ; try acb; subst needed rz; pose proof (rz_size_facts size); unfold round_up; Z.div_mod_to_equations; lia);
    assert (ALN : exists thq sbq rzk ck nk, TH = 16 * thq /\ sb = 65536 * sbq /\ rz = 16 * rzk /\ csz = 32 * ck /\ needed - rz = 8 * nk)
      by (clear - RNG SBR HC DCSZ DNEED DRZ; try acb; destruct RNG as [RNG']; destruct SBR as [SBR']; pose proof (rz_size_facts size);
          pose proof (class_size_table_facts c ltac:(hci; lia)); subst csz needed rz; unfold round_up;
          exists (TH / 16), (sb / 65536), (rz_size size / 16), (class_size c / 32), ((size `max` 8 + 64 - 1) / 64 * 8 + 8);
          Z.div_mod_to_equations; lia);
    destruct ALN as (thq & sbq & rzk & ck & nk & ALN);
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD')));
    assert (EQS : U = AB + rz /\ P = TH + 208 + 80 * c /\ AB = sb + c * 4294967296 + cp * 16 /\ n = Z.of_nat (length T) /\ CA = TH + 208)
      by (rewrite DU, DP, DAB, DN, DCA; repeat split; reflexivity);
    assert (EQh : hidden (c = class_id needed /\ csz = class_size c /\ rz = rz_size size /\ needed = round_up (Z.max size 8) 64 + 64 + rz
                       /\ cp = hd 0 chunks /\ id = d_putid d (depot_hash T))) by (constructor; repeat split; assumption);
    assert (C8F : 8 * csz8 = csz /\ 1 <= fl <= size /\ fl <= 4096) by (clear - ALN SZ DC8 DFL; try acb; subst csz8 fl; Z.div_mod_to_equations; lia);
    assert (FLh : hidden (fl = Z.min size 4096)) by (constructor; exact DFL);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    assert (SHR : 2201439137792 <= sh AB /\ sh AB + csz8 <= 17594333495296) by (clear - BND C8F; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    assert (LENQ : Z.of_nat (length (wlist (rev (tl chunks)))) = cnt - 1)
      by (clear - CNT HIT; try acb; unfold wlist; rewrite length_map, length_rev; destruct chunks;
          [unfold zlen in CNT; cbn in CNT; lia| cbn [tl]; unfold zlen in CNT; cbn [length] in CNT; lia]);
    (* [comment removed for export] *)
    clear DRZ DNEED DC DCSZ DC8 DFL DCA DP DCP DAB DU DN DID.

  (* [comment removed for export] *)
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
  Ltac remregF n name eqname folded :=
    remreg n name eqname; match type of eqname with ?e = _ => change (e = folded) in eqname end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac dlia := lazymatch goal with |- _ <= _ \/ _ <= _ => lia | |- _ \/ _ => first [ left; dlia | right; dlia ] | |- _ /\ _ => split; dlia | |- _ => lia end.
  Ltac splia := lazymatch goal with |- _ /\ _ => split; splia | |- _ => plia end.
  Ltac slia ::= first [ exact I | dlia | splia ].

  Lemma partC : forall (x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) (mB : mem) (j8 : list byte),
    AENV tp TSD CTX TH sb SO T rest mB -> mem_inv asegs mB -> munch W m mB -> wmono asegs m mB ->
    AFR mB j8 -> stk asegs mB lo (bv_unsigned sp + -128) ->
    rw_cells asegs mB P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs mB (P + 8) [C8 (wz csz)] -> u32arr asegs mB (P + 16) (wlist (rev chunks)) ->
    stk asegs mB (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs mB (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs mB AB (AB + csz) ->
    u8arr asegs mB (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs mB (TH + 2800) (TH + 3168) ->
    DEPOT asegs d mB ->
    evt asegs POST
      (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -128)) gp tp x5 x6 x7 (wz 64) (wz 0) (wz (Z.max size 8)) (wz 8) x12 x13 x14 x15 x16 x17
               (wz 64) (wz (rz_log size)) (wz 0x10000) (wz size) (wz AINST) (wz SO) (wz 0xffff) (wz 63) (wz (AINST + 2047)) (wz 1) x28 x29 x30 x31)
          F (Z_to_bv 64 0x196fb0) fc None mB (seg_rom asegs)).
  Proof.
    intros until j8. intros ENV MI MU WM FR ST QC1 QC2 QC3 QC4 QST CHUNK SHK TST DEP.
    (* [comment removed for export] *)
    pose proof (munch_refl W mB) as MUB. pose proof (wmono_refl asegs mB) as WMB. unfold W in MUB. pose proof ENV as ENV0.
    unfold W in MU. prep. open_env ENV. unfold AFR, aframeAl in FR. unfold wz in *. unfold AINST.
    assert (MX : 8 <= Z.max size 8 /\ size <= Z.max size 8 /\ Z.max size 8 <= needed) by (clear - SZ RZB; try acb; lia).
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (clear - CNT; try acb; unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    remember (Z.max size 8) as mx eqn:EMX in MX |- *. assert (MXh : hidden (mx = Z.max size 8)) by (constructor; exact EMX). clear EMX.
    assert (RZL : 0 <= rz_log size <= 7 /\ rz = Z.shiftl 16 (rz_log size)).
    { unhide_hyp EQh. destruct EQh as (_ & _ & ERZ & _). rewrite ERZ. unfold rz_size, kMinRedzoneLog, kMaxRedzoneLog, rz_log.
      repeat match goal with |- context [if ?b then _ else _] => destruct b end; cbn; split; try (lia_guard; (lia_guard; first [clear; lia | lia])); reflexivity. }
    destruct RZL as [RZL1 RZL2].
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x 18446744073709551552 + ?y)] =>
      replace (Z_to_bv 64 (Z.land x 18446744073709551552 + y)) with (Z_to_bv 64 (needed - rz)) end.
    2:{ f_equal. replace (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 64) 9) + -1))) 64) with 64 by (vm_compute; reflexivity).
        rewrite (unsigned_lit (mx + 63)) by lia. change 18446744073709551552 with (2^64 - 2^6)%Z. rewrite StrFun.land_align_down by lia.
        unhide_hyp EQh. unhide_hyp MXh. destruct EQh as (_ & _ & _ & EN & _). rewrite EN. subst mx. unfold round_up. clear.
        pose proof (Z.le_max_r size 8). Z.div_mod_to_equations. lia. }
    match goal with |- context [Z_to_bv 64 (Z.land ?x 64)] => replace (Z_to_bv 64 (Z.land x 64)) with (Z_to_bv 64 64) by (apply bv_eq; vm_compute; reflexivity) end.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K.
    { exfalso. apply K. rewrite ?unsigned_lit by lia. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. change (2^3) with 8. clear - ALN RZB; try acb. lia. }
    clear K.
    (* [comment removed for export] *)
    step. step. replace (v_sltiu (Z_to_bv 64 size) 1) with (Z_to_bv 64 0).
    2:{ rewrite v_sltiu_b2z. rewrite (unsigned_lit size) by lia. change (bv_wrap 64 1) with 1. rewrite zb_b2z_if. destruct (Z.ltb_spec size 1); [lia| reflexivity]. }
    (* [comment removed for export] *)
    step. step. match goal with |- context [Z_to_bv 64 (bv_swrap 32 ?x)] => replace (Z_to_bv 64 (bv_swrap 32 x)) with (Z_to_bv 64 rz) end.
    2:{ f_equal. rewrite (unsigned_lit (rz_log size)), Z.mod_small by lia. rewrite <- RZL2. symmetry. apply swrap32_small. lia. }
    (* [comment removed for export] *)
    step. step. step. replace (v_sltu (Z_to_bv 64 64) (Z_to_bv 64 65537)) with (Z_to_bv 64 1) by (apply bv_eq; vm_compute; reflexivity).
    step. replace (needed - rz + rz) with needed by lia.
    (* [comment removed for export] *)
    step. replace (v_sltu (Z_to_bv 64 needed) (Z_to_bv 64 65537)) with (Z_to_bv 64 1).
    2:{ rewrite v_sltu_b2z. rewrite (unsigned_lit needed), (unsigned_lit 65537) by (first [clear - SPR BND CSZ RZB ALN; lia | lia]). rewrite zb_b2z_if. destruct (Z.ltb_spec needed 65537); [reflexivity| unfold kMaxSize in SZ; lia]. }
    step. step. step. step. step. rewrite Z.land_0_l, Z.add_0_l.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. unfold kMaxSize in SZ. lia. } clear K.
    step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. unfold kMaxSize in SZ. lia. } clear K.
    step. step. if_cases K; zify_cond K. 2:{ exfalso. revert K. rewrite ?unsigned_lit by lia. unfold kMaxSize in SZ. lia. } clear K.
    (* [comment removed for export] *)
    step. callD getcurthread_spec. all: rewrite ?unsigned_lit by lia. all: try eassumption; try (lia_guard; (lia_guard; first [clear - HI BND ALN; lia | lia])).
    all: try (unfold ATSDINIT; eassumption). all: try (acb; (lia_guard; (lia_guard; lia))). all: try (unfold AIMG_TOP; lia).
    unfold wz.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    step. step. step. step. step.
    destruct EQS as (EU & EP & EAB & En & ECA). unhide_hyp EQh. destruct EQh as (Ec & Ecsz & Erz & Eneeded & Ecp & Eid).
    assert (CAR : akobj CA 2592 /\ CA + 2592 <= aceil /\ CA mod 16 = 0)   (* [comment removed for export] *)
      by (match goal with TB : akobj TH 4096 |- _ => clear - ECA BND ALN TB end; try acb; subst CA; split; [eapply akobj_sub; [eassumption| lia| lia] | Z.div_mod_to_equations; lia]).
    callD (combined_hit_specP _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc _ lo needed CA sb cnt mc chunks j0 j1 j2 j3 c P csz)
      by (rewrite ?unsigned_lit by (first [clear - BND HI; lia | lia]); try eassumption; try (lia_guard; (lia_guard; first [clear - SPR BND CSZ EP ECA HI ALN SPQ SZ RZB; lia | lia])); try (unfold wz; f_equal; (lia_guard; (lia_guard; first [clear - SPR BND CSZ ECA; lia | lia])));
          try (rewrite ECA; unfold CACHE_STATS; eassumption)).
    all: try (clear - SPQ; try acb; Z.div_mod_to_equations; lia).
    all: try (clear - BND; try acb; unfold kSpaceSize; lia).   (* [comment removed for export] *)
    replace (wz (sb + c * 2 ^ 32 + hd 0 chunks * 16)) with (Z_to_bv 64 AB) by (unfold wz; f_equal; rewrite EAB, Ecp; lia).
    clear QC3. unfold CACHE_STATS in *.
    lazymatch goal with H : rw_cells asegs _ (CA + 2560) _ |- _ => rewrite ECA in H; rename H into QSTn end.
    (* [comment removed for export] *)
    clear Etsdi Etp Etsd Ectx Elsan Egot2 Ethr Etid Einit Eafl Ecan Egot Eshb Ehme Ethresh Erms Efill Epart Ehooks Einst1 Einst2 Eso Etr.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (munch_refl W2 mm) as MUC; pose proof (wmono_refl asegs mm) as WMC; unfold W2 in MUC end.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    step. rewrite <- EU.
    step. rewrite (unsigned_lit U) by (first [clear - HI SPR BND CSZ RZB ALN EU EAB Ec Ecp; lia | lia]). change 63 with (Z.ones 6). rewrite Z.land_ones by lia. change (2^6) with 64.
    replace (U mod 64) with 0 by (clear - EU ABA RZ64; destruct ABA as [ABA'], RZ64 as [RZ64']; Z.div_mod_to_equations; lia).   (* [comment removed for export] *)
    step. step. if_cases K. 2:{ exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. if_cases K; zify_cond K. { exfalso. rewrite ?unsigned_lit in K by lia. lia. } clear K.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ AB (U + -16) (AB + csz) CHUNK ltac:(hci; lia)) as [CHL CH2]. clear CHUNK.
    destruct (stk_split asegs _ (U + -16) U (AB + csz) CH2 ltac:(hci; lia)) as [CH3 USR]. clear CH2.
    destruct (stk_cells _ _ _ CH3 ltac:(hci; lia)) as [hj HDR]. clear CH3. replace (U - (U + -16)) with 16 in HDR by lia. change (Z.to_nat 16) with 16%nat in HDR.
    assert (LHJ : length hj = 16%nat) by (destruct HDR as [[WF _] _]; exact (proj1 WF)).
    destruct hj as [|ob0 [|ob1 hj']]; [cbn in LHJ; lia| cbn in LHJ; lia|].
    apply (rw_cells_split_CB asegs _ _ [] 16 (ob0 :: ob1 :: hj') [] [1;1;2;4;8]%nat) in HDR; [| reflexivity].
    cbn [mk_CB_cells firstn skipn app] in HDR. change (take 0 hj') with (@nil byte) in HDR. change (drop 0 hj') with hj' in HDR.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    rewrite (unsigned_lit size) by lia. rewrite (Z.shiftr_div_pow2 size 32), (Z.shiftr_div_pow2 size 48) by lia.
    replace (size / 2 ^ 32) with 0 by (symmetry; apply Z.div_small; unfold kMaxSize in SZ; lia).
    replace (size / 2 ^ 48) with 0 by (symmetry; apply Z.div_small; unfold kMaxSize in SZ; lia).
    unfold zxb. pose proof (bv_unsigned_in_range _ ob1) as OB1. change (bv_modulus 8) with 256 in OB1.
    remember (bv_unsigned ob1) as o1 eqn:EO1. clear EO1.
    match goal with |- context [Z_to_bv 64 (Z.lor ?x 1)] => remember (Z.lor x 1) as x1v eqn:EX1 end.
    rewrite (unsigned_lit o1) in EX1 by lia. change 18446744073709551612 with (2^64 - 2^2)%Z in EX1. rewrite StrFun.land_align_down in EX1 by lia.
    rewrite unsigned_lit in EX1 by (clear - OB1; try acb; Z.div_mod_to_equations; lia).
    assert (X1R : 0 <= x1v < 256).
    { subst x1v. change 256 with (2^8). apply lor_lt_pow2; [| lia]. clear - OB1; try acb. Z.div_mod_to_equations. lia. }
    assert (X1h : hidden (x1v = Z.lor (o1 - o1 mod 2 ^ 2) 1)) by (constructor; exact EX1). clear EX1.
    (* [comment removed for export] *)
    st1. st1. step. step. if_cases K. { exfalso. revert K. vm_compute. discriminate. } clear K.
    (* [comment removed for export] *)
    step. step. step. step. st1.
    rewrite (unsigned_lit x1v) in * by lia.
    assert (L143 : 0 <= Z.land x1v 143 < 256) by (split; [apply Z.land_nonneg; lia| change 256 with (2^8); apply land_lt_pow2; lia]).
    rewrite (unsigned_lit (Z.land x1v 143)) in * by lia.
    remember (Z.lor (Z.land x1v 143) 64) as hb1 eqn:EHB in *.   (* [comment removed for export] *)
    assert (HB1F : 0 <= hb1 < 256 /\ b1_ok (Z.land hb1 243)).
    { unhide_hyp X1h. subst hb1 x1v. exact (hb1Al_facts o1 OB1). }
    replace (hb1 mod 256) with hb1 in HDR by (symmetry; apply Z.mod_small; (first [clear - HB1F; lia | lia])).
    clear X1h L143 EHB X1R x1v OB1 o1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (ENV' : AENV tp TSD CTX TH sb SO T rest mm)
        by (eapply aenv_now0 with (cnt := cnt) (chunks := chunks) (n := n) (rz := rz) (c := c) (cp := cp) (fl := fl) (U := U) (id := id)
                                   (needed := needed) (csz := csz) (csz8 := csz8) (CA := CA) (P := P) (AB := AB) (d := d) (lo := lo) (m0 := mB);
            try exact ENV0; try exact MUB; try exact WMB; try exact DEFS; eassumption) end.
    clear ENV0 MUB WMB. open_env ENV'. unfold wz in *.
    (* [comment removed for export] *)
    step. if_cases K; zify_cond K. { exfalso. revert K. rewrite ?unsigned_lit by lia. lia. } clear K.
    step. step. step. step.
    replace (Z_to_bv 64 (bv_unsigned (sx32 (Z_to_bv 64 0)) ≪ 32)) with (Z_to_bv 64 0) by (apply bv_eq; vm_compute; reflexivity).
    apply rw_cells_CB1 in HDR. destruct HB1F as [HB1R HB1M]. unhide_hyp MXh. subst mx.
    eapply partC2; try eassumption; try reflexivity; try (econstructor; [exact Etsdi | exact Etp | exact Etsd | exact Ectx | exact Elsan | exact Egot2 | exact Ethr | exact Etid | exact Einit | exact Eafl | exact Ecan | exact Egot | exact Eshb | exact Ehme | exact Ethresh | exact Erms | exact Efill | exact Epart | exact Ehooks | exact Einst1 | exact Einst2 | exact Eso | exact Etr]); try lia.
  Qed.

End Alloc.
