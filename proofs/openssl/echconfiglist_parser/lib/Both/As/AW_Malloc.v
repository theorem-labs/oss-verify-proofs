(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
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
     AsDepotInv AsDepotHash AsDepotPut AsUnwind CidBits AW_Combined AW_PoisonShadow AW_Leaves AW_DepotFrame AW_AllocBase AW_Allocate AllocWalkKit.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Unset Keyed Unification.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AW_MallocBase AW_Malloc1 AllocTacX.
From OssFuzzTheorems.Proofs.openssl.echconfiglist_parser.lib.Both.As Require Import AllocStoreDj.   (* [comment removed for export] *)
Local Ltac transport_chunks segs m a bs ::= transport_chunks_rx8 segs m a bs.   (* [comment removed for export] *)

Section Icpt.
  Context {HCEIL : HeapCeil}.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo size : Z) (d : depot).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)).
  Variables (sb cnt mc : Z) (chunks : list Z) (j0 j1 j2 j3 : word).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x1bf41c (bv_unsigned sp) TOP BOT 30 CHI.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (rz needed c csz csz8 fl CA P cp AB U n id : Z).
  Hypothesis DEFS : hidden (rz = rz_size size /\ needed = round_up (Z.max size 8) 8 + rz /\ c = class_id needed /\ csz = class_size c
                            /\ csz8 = csz / 8 /\ fl = Z.min size 4096 /\ CA = TH + 208 /\ P = CA + 80 * c /\ cp = hd 0 chunks
                            /\ AB = sb + c * 2^32 + cp * 16 /\ U = AB + rz /\ n = Z.of_nat (length T) /\ id = d_putid d (depot_hash T)).
  Let W : list ivl := (lo, (bv_unsigned sp)) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3169) :: depot_W d.
  Let W2 : list ivl := (lo, (bv_unsigned sp)) :: (P, P + 4) :: (CA + 2576, CA + 2584) :: (AB, AB + csz) :: (sh AB, sh AB + csz8)
                      :: (TH + 2800, TH + 3169) :: nil.
  Let POST := malloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m W lo size AB U rz csz P cnt mc TH id chunks
                          (d_put d (depot_hash T) n).

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
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
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  Hypothesis Ha0 : a0 = wz size.

  Ltac prepI :=
    pose proof DEFS as DEFS'; destruct DEFS' as [(DRZ & DNEED & DC & DCSZ & DC8 & DFL & DCA & DP & DCP & DAB & DU & DN & DID)];
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    pose proof (bv_unsigned_in_range _ ra) as RAR; change (bv_modulus 64) with (2^64)%Z in RAR;
    pose proof (bv_unsigned_in_range _ s0) as S0R; change (bv_modulus 64) with (2^64)%Z in S0R;
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
                       /\ cp = hd 0 chunks /\ id = d_putid d (depot_hash T) /\ T = utrace 0x1bf41c (bv_unsigned sp) TOP BOT 30 CHI
                       /\ CHI = icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH /\ csz8 = csz / 8)) by (constructor; repeat split; first [assumption | reflexivity]);
    assert (C8F : 8 * csz8 = csz) by (clear - ALN DC8; try acb; subst csz8; Z.div_mod_to_equations; lia);
    assert (PB : TH + 288 <= P /\ P + 80 <= TH + 2768) by (clear - HC EQS; try acb; lia);
    assert (SHR : 2201439137792 <= sh AB /\ sh AB + csz8 <= 17594333495296) by (clear - BND C8F; try acb; unfold sh, ASHADOW_BASE; Z.div_mod_to_equations; lia);
    assert (NR : 1 <= n <= 30) by (rewrite DN; unfold T; apply utrace_length; lia);
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

  (* [comment removed for export] *)
  Theorem malloc_spec :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m P [C4 (wz cnt); C4 (wz mc)] -> rw_cells asegs m (P + 8) [C8 (wz csz)] -> u32arr asegs m (P + 16) (wlist (rev chunks)) ->
    stk asegs m (P + 16 + 4 * cnt) (P + 80) -> rw_cells asegs m (TH + 208 + 2560) [C8 j0; C8 j1; C8 j2; C8 j3] ->
    stk asegs m AB (AB + csz) ->
    u8arr asegs m (sh AB) (repeat (b8 0xfa) (Z.to_nat csz8)) ->
    stk asegs m (TH + 2800) (TH + 3168) -> rw_cells asegs m (TH + 3168) [C1 (b8 0)] ->
    DEPOT asegs d m ->
    evt asegs POST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bf354) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST QC1 QC2 QC3 QC4 QST CHUNK SHK TST UNW DEP. rewrite Ha0.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    (* [comment removed for export] *)
    pose proof (munch_refl W2 m) as MUC. pose proof (wmono_refl asegs m) as WMC. unfold W2 in MUC.
    unfold W in MU. prepI.
    assert (LENC : Z.of_nat (length (wlist (rev chunks))) = cnt) by (clear - CNT; try acb; unfold wlist; rewrite length_map, length_rev; unfold zlen in CNT; lia).
    assert (SHKL : Z.of_nat (length (repeat (b8 250) (Z.to_nat csz8))) = csz8) by (rewrite repeat_length; lia).
    (* [comment removed for export] *)
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp) ST ltac:(hci; lia)) as [ST' TOPST]. clear ST. rename ST' into ST.
    destruct (stk_cells _ _ _ TOPST ltac:(hci; lia)) as [fj FRW]. clear TOPST.
    replace (bv_unsigned sp - (bv_unsigned sp + -2128)) with 2128 in FRW by lia. change (Z.to_nat 2128) with 2128%nat in FRW.
    apply (rw_cells_split_CB asegs _ _ [] 2128 fj [] [8;8;2040;8;8;56]%nat) in FRW; [| reflexivity].
    cbn [mk_CB_cells app] in FRW.
    (* [comment removed for export] *)
    repeat match type of FRW with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FRW end.
    repeat match goal with H : _ = take _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_; _; _; _; _] [_])) in FRW. destruct FRW as [FRA FRB]. cbn [cells_size csize Nat.add] in FRB.
    replace (bv_unsigned sp + -2128 + Z.of_nat 2072) with (bv_unsigned sp + -56) in FRB by (clear; lia).
    step. do 7 step.
    lazymatch type of FRA with rw_cells _ ?mmq ?Aq ?csA =>
      lazymatch type of FRB with rw_cells _ _ _ ?csB =>
        assert (FRW : rw_cells asegs mmq Aq (csA ++ csB))
          by (apply (proj2 (rw_cells_app asegs _ _ _ _)); split; [exact FRA|]; cbn [cells_size csize Nat.add];
              replace (bv_unsigned sp + -2128 + Z.of_nat 2072) with (bv_unsigned sp + -56) by (clear; lia); exact FRB) end end.
    cbn [app] in FRW. clear FRA FRB.
    step. step. step. step.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (IEcur : IENV tp TSD CTX TH sb TOP BOT mm) by (eapply ienv_now with (size := size) (d := d) (CH := CH) (rz := rz) (needed := needed) (c := c) (csz := csz) (csz8 := csz8) (fl := fl) (CA := CA) (P := P) (cp := cp) (AB := AB) (U := U) (n := n) (id := id) (lo := lo) (chunks := chunks) (ra := ra) (s0 := s0); try exact ENV; try exact MU; try exact WM; try exact DEFS; eassumption) end.
    pose proof (i_init _ _ _ _ _ _ _ _ IEcur) as Einit. clear IEcur.
    step. callD try_asan_init_spec. all: try (unfold AINITED; eassumption). all: rewrite ?unsigned_lit by lia. all: try eassumption; try lia.
    clear Einit.
    step. if_cases K; [exfalso; revert K; vm_compute; discriminate|]. clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. st1. step. st1.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (IEcur : IENV tp TSD CTX TH sb TOP BOT mm) by (eapply ienv_now with (size := size) (d := d) (CH := CH) (rz := rz) (needed := needed) (c := c) (csz := csz) (csz8 := csz8) (fl := fl) (CA := CA) (P := P) (cp := cp) (AB := AB) (U := U) (n := n) (id := id) (lo := lo) (chunks := chunks) (ra := ra) (s0 := s0); try exact ENV; try exact MU; try exact WM; try exact DEFS; eassumption) end.
    pose proof (i_mcs _ _ _ _ _ _ _ _ IEcur) as Emcs. clear IEcur.
    step. callD malloc_context_size_spec. all: try eassumption.
    step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    step. step. step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (IEcur : IENV tp TSD CTX TH sb TOP BOT mm) by (eapply ienv_now with (size := size) (d := d) (CH := CH) (rz := rz) (needed := needed) (c := c) (csz := csz) (csz8 := csz8) (fl := fl) (CA := CA) (P := P) (cp := cp) (AB := AB) (U := U) (n := n) (id := id) (lo := lo) (chunks := chunks) (ra := ra) (s0 := s0); try exact ENV; try exact MU; try exact WM; try exact DEFS; eassumption) end.
    pose proof (i_got _ _ _ _ _ _ _ _ IEcur) as Egot. clear IEcur. unfold AGOT_VALS in Egot. cbn [map] in Egot. unfold wz in Egot.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => assert (IEcur : IENV tp TSD CTX TH sb TOP BOT mm) by (eapply ienv_now with (size := size) (d := d) (CH := CH) (rz := rz) (needed := needed) (c := c) (csz := csz) (csz8 := csz8) (fl := fl) (CA := CA) (P := P) (cp := cp) (AB := AB) (U := U) (n := n) (id := id) (lo := lo) (chunks := chunks) (ra := ra) (s0 := s0); try exact ENV; try exact MU; try exact WM; try exact DEFS; eassumption) end.
    pose proof (i_cfu _ _ _ _ _ _ _ _ IEcur) as Ecfu. clear IEcur. replace (7586856 + 34) with 7586890 in Ecfu by reflexivity.
    step. step. step. step. clear Egot Ecfu.
    (* [comment removed for export] *)
    step. callD malloc_context_size_spec. all: try eassumption. clear Emcs.
    step. step. step. step. step.
    match goal with |- context [Z_to_bv 64 (Z.land ?x (bv_unsigned sp))] =>
      replace (Z.land x (bv_unsigned sp)) with (bv_unsigned sp)
        by (replace x with (Z.ones 64) by (vm_compute; reflexivity); rewrite Z.land_comm, Z.land_ones, Z.mod_small by lia; reflexivity) end.
    step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    step. step. step. step. step. step.
    (* [comment removed for export] *)
    eapply icpt2; try eassumption; try reflexivity; try lia.
  Qed.
End Icpt.
