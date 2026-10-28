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
Definition free_pre_post (ra sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (m : mem) (lo TSD CTX TH sb TOP BOT : Z) (T : list Z) (d : depot) : machine_state -> Prop :=
  fun ms' => exists (x3 x4 x5 x12 x13 x14 x15 x16 x17 : word) (jk : list byte) (rest : list word) m',
    ms' = MS (mkR (wz 0x1bf32c) (Z_to_bv 64 (bv_unsigned sp + -2128)) gp tp x3 x4 x5 sp a0 (wz AINST) a0 (wz 0) (wz 0)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (wz 1) x12 x13 (wz 0x1bf2bc) (wz 1)
                  (Z_to_bv 64 (bv_unsigned sp + -2128)) (Z_to_bv 64 (bv_unsigned sp + -81)) s6 s7 s8 s9 s10 s11 x14 x15 x16 x17)
             F (Z_to_bv 64 0x196ae8) fc None m' (seg_rom asegs)
    /\ munch [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (AIAINIT, AIAINIT + 4); (AIAINST, AIAINST + 0x81030)] m m'
    /\ wmono asegs m m' /\ mem_inv asegs m'
    /\ IENV tp TSD CTX TH sb TOP BOT m'
    /\ stk asegs m' lo (bv_unsigned sp + -2128)
    /\ rw_cells asegs m' (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]
    /\ u64arr asegs m' (bv_unsigned sp + -2128 + 16) (map wz T ++ rest) /\ length rest = (255 - length T)%nat
    /\ rw_cells asegs m' (bv_unsigned sp + -72) [C8 sp]
    /\ rw_cells asegs m' (bv_unsigned sp + -64) [CB 8 jk; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]
    /\ rw_cells asegs m' (TH + 3168) [C1 (b8 0)]
    /\ DEPOT asegs d m'
    /\ Forall (fun x => 0 <= x < 2^64) T /\ (1 <= length T <= 30)%nat
    /\ rw_cells asegs m' AIAINIT [C1 (b8 1); C1 (b8 0); C2 (wz 0)]
    /\ ia_after m'.

(* [comment removed for export] *)
Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l h] W IH]; intros a n a' n' D H1 H2; [exact I|].
  destruct D as [D1 D2]. split; [lia| eapply IH; eauto].
Qed.

(* [comment removed for export] *)
Lemma ia_if_transport : forall (inited : bool) W0 m1 m2, (if inited then ia_after m1 else ia_pristine m1) -> munch W0 m1 m2 -> wmono asegs m1 m2 ->
  disjoint_from W0 6994688 0x81030 -> (if inited then ia_after m2 else ia_pristine m2).
Proof.
  intros inited W0 m1 m2 H MU0 WM0 D. unfold ia_after, ia_pristine, AIAINST in *. destruct inited.
  - destruct H as (H1 & H2 & H3).
    split; [| split].
    + eapply u8arr_transport; [exact H1| exact MU0| exact WM0|]. rewrite repeat_length, Z2Nat.id by lia.
      eapply disjoint_from_sub; [exact D| lia| lia].
    + eapply rw_cells_transport; [exact H2| exact MU0| exact WM0|]. cbn [cells_size csize Nat.add].
      eapply disjoint_from_sub; [exact D| lia| lia].
    + eapply u8arr_transport; [exact H3| exact MU0| exact WM0|]. rewrite repeat_length, Z2Nat.id by lia.
      eapply disjoint_from_sub; [exact D| lia| lia].
  - eapply u8arr_transport; [exact H| exact MU0| exact WM0|]. rewrite repeat_length, Z2Nat.id by lia. exact D.
Qed.

(* [comment removed for export] *)
Lemma ia_probe_read : forall m1 K i, u8arr asegs m1 6994688 (repeat (b8 0) K) -> 0 <= i -> i + 8 <= Z.of_nat K ->
  ov_read_bytes asegs m1 (wa (6994688 + i)) 8 = Some (le8 (wz 0)).
Proof.
  intros m1 K i [B _] Hi HK. rewrite (bytes_at_read asegs m1 6994688 _ i 8 B Hi) by (rewrite repeat_length; lia).
  rewrite skipn_repeat', firstn_repeat'. rewrite le8_zero. f_equal. f_equal. lia.
Qed.
End HCW.

Section Pre.
  Context {HCEIL : HeapCeil}.
  Local Unset Keyed Unification.
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem).
  Variables (lo : Z) (d : depot) (inited : bool).
  Variables (TSD CTX TH TOP BOT : Z) (CH : list (Z * Z)).
  Variable (sb : Z).
  Let CHI := icpt_chain (bv_unsigned ra) (bv_unsigned s0) (bv_unsigned sp) TOP CH.
  Let T := utrace 0x1bf2bc (bv_unsigned sp) TOP BOT 30 CHI.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Let W : list ivl := [(lo, bv_unsigned sp); (TH + 3168, TH + 3169); (7578504, 7578504 + 4); (6994688, 6994688 + 0x81030)].
  Let PREPOST := free_pre_post ra sp gp tp a0 s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo TSD CTX TH sb TOP BOT T d.

  Hypothesis LO : aceil <= lo.  Hypothesis HI : lo + 2496 <= bv_unsigned sp.
  Hypothesis SPA : hidden (bv_unsigned sp mod 16 = 0).
  Hypothesis SPT : hidden (bv_unsigned sp + 16 <= 2^47).
  Hypothesis P47 : bv_unsigned a0 < 2^47.
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
  Hypothesis TBR : hidden (4096 <= TOP <= 2^47 /\ 0 <= BOT < TOP).
  Hypothesis DLO : d_nb d + 16 * 65536 <= lo /\ d_sb d + 8 * 131072 <= lo.
  (* [comment removed for export] *)
  Hypothesis FCH : goodframe BOT (bv_unsigned sp) TOP = true -> goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true ->
                   bv_unsigned sp + 16 <= bv_unsigned s0 /\ frame_chain asegs m TOP (bv_unsigned s0) CH.
  (* [comment removed for export] *)
  Hypothesis FLG : rw_cells asegs m AIAINIT [C1 (b8 (if inited then 1 else 0)); C1 (b8 0); C2 (wz 0)].
  Hypothesis IA : if inited then ia_after m else ia_pristine m.

  Ltac prepI :=
    pose proof (bv_unsigned_in_range _ sp) as SPR; change (bv_modulus 64) with (2^64)%Z in SPR;
    pose proof (bv_unsigned_in_range _ ra) as RAR; change (bv_modulus 64) with (2^64)%Z in RAR;
    pose proof (bv_unsigned_in_range _ s0) as S0R; change (bv_modulus 64) with (2^64)%Z in S0R;
    pose proof (bv_unsigned_in_range _ a0) as A0R; change (bv_modulus 64) with (2^64)%Z in A0R;
    assert (BND : aceil <= lo /\ 12109808 <= TSD /\ TSD + 8 <= 12599296 /\ 12599296 <= CTX /\ CTX + 160 <= aceil
               /\ 4096 <= TH /\ TH + 4096 <= aceil /\ 12109896 <= bv_unsigned tp /\ bv_unsigned tp + 4096 <= 12599296
               /\ bv_unsigned sp + 16 <= 140737488355328 /\ 4096 <= TOP /\ TOP <= 140737488355328 /\ 0 <= BOT /\ BOT < TOP)
      by (clear - LO RNG TPR SPT TBR; try acb; destruct RNG as [RNG']; destruct TPR as [TPR'];
          destruct SPT as [SPT']; destruct TBR as [TBR']; unfold akobj, alow1, aapp, aapp_lo, aapp_hi, AIMG_LO, ALOWSH_LO in *; unfold AHI_LO, kSpaceSize, AIMG_TOP in *;
          acb; change (2^47)%Z with 140737488355328%Z in SPT', TBR'; lia);
        region_sides; name_bands;
    assert (SPQ : exists spq, bv_unsigned sp = 16 * spq) by (clear - SPA; try acb; destruct SPA as [SPA']; exists (bv_unsigned sp / 16); Z.div_mod_to_equations; lia);
    destruct SPQ as [spq SPQ];
    assert (PLCh : hidden PLACED) by (destruct PLC as [PLC']; destruct PLCD as [PLCD']; exact (Hide _ (conj PLC' PLCD'))).

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
  Lemma ienv_now_fpre : forall m1, IENV tp TSD CTX TH sb TOP BOT m -> munch W m m1 -> wmono asegs m m1 -> IENV tp TSD CTX TH sb TOP BOT m1.
  Proof.
    intros m1 E MU WM. unfold W in MU. prepI. open_ienv E.
    constructor; unfold AGOT_VALS; cbn [map repeat];
      (eapply rw_cells_transport; [eassumption| exact MU| exact WM| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; slia]).
  Qed.

  Theorem free_pre :
    IENV tp TSD CTX TH sb TOP BOT m -> mem_inv asegs m -> stk asegs m lo (bv_unsigned sp) ->
    rw_cells asegs m (TH + 3168) [C1 (b8 0)] ->
    DEPOT asegs d m ->
    evt asegs PREPOST
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x1bf184) fc None m (seg_rom asegs)).
  Proof.
    intros ENV MI ST UNW DEP.
    pose proof (munch_refl W m) as MU. pose proof (wmono_refl asegs m) as WM.
    pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU2.   (* [comment removed for export] *)
    unfold W in MU. prepI. unfold AIAINIT in FLG.
    (* [comment removed for export] *)
    destruct (stk_split asegs _ lo (bv_unsigned sp + -2128) (bv_unsigned sp) ST ltac:(hci; lia)) as [ST' TOPST]. clear ST. rename ST' into ST.
    destruct (stk_cells _ _ _ TOPST ltac:(hci; lia)) as [fj FRW]. clear TOPST.
    replace (bv_unsigned sp - (bv_unsigned sp + -2128)) with 2128 in FRW by lia. change (Z.to_nat 2128) with 2128%nat in FRW.
    apply (rw_cells_split_CB asegs _ _ [] 2128 fj [] [8;8;2040;8;8;56]%nat) in FRW; [| reflexivity].
    cbn [mk_CB_cells app] in FRW.
    repeat match type of FRW with context [CB ?n (take ?k ?l)] => let J := fresh "jk" in remember (take k l) as J in FRW end.
    repeat match goal with H : _ = take _ _ |- _ => clear H end.
    (* [comment removed for export] *)
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F0 FRW]. cbn [cells_size csize Nat.add] in FRW.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F1 FRW]. cbn [cells_size csize Nat.add] in FRW.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F2 FRW]. cbn [cells_size csize Nat.add] in FRW.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in FRW. destruct FRW as [F3 F4]. cbn [cells_size csize Nat.add] in F4.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8) with (bv_unsigned sp + -2120) in F1 by lia.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 8) with (bv_unsigned sp + -2112) in F2 by lia.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2040) with (bv_unsigned sp + -72) in F3 by lia.
    replace (bv_unsigned sp + -2128 + Z.of_nat 8 + Z.of_nat 8 + Z.of_nat 2040 + Z.of_nat 8) with (bv_unsigned sp + -64) in F4 by lia.
    (* [comment removed for export] *)
    step. do 7 step. step. step. step. step.
    (* [comment removed for export] *)
    pose proof (ienv_now_fpre _ ENV MU WM) as E0.
    pose proof (i_got _ _ _ _ _ _ _ _ E0) as Egot. unfold AGOT_VALS in Egot. cbn [map] in Egot.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in Egot. destruct Egot as [GOTP _].
    pose proof (i_psc _ _ _ _ _ _ _ _ E0) as PSC. clear E0.
    lazymatch goal with H : wmono asegs m ?mm |- _ =>
      pose proof (ia_if_transport inited _ m mm IA MU2 H ltac:(hci; cbn [disjoint_from]; lia)) as IA0 end.
    clear IA MU2.
    step.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with H : stk asegs mm lo _ |- _ =>
      eapply evt_cut; [eapply (internal_allocator_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc mm lo inited);
         [exact MI| | | | exact FLG| exact IA0| exact GOTP| exact PSC]
      | clear FLG IA0 GOTP PSC; let ms := fresh "ms" in let PO := fresh "PO" in intros ms PO; unfold ia_post, AIAINIT, AIAINST in PO;
        rewrite ?unsigned_lit in PO by lia; revert ms PO; post_call asegs mm ] end end.
    all: rewrite ?unsigned_lit by lia. 1: eassumption. 1,2: lia.
    lazymatch goal with H : rw_cells asegs _ 7578504 _ |- _ => rename H into FLG end.
    lazymatch goal with H : ia_after _ |- _ => rename H into IA1 end.
    assert (FLGh : True -> rw_cells asegs _ 7578504 [C1 (b8 1); C1 (b8 0); C2 (wz 0)]) by (intros _; exact FLG). clear FLG.
    rename PC into ST. rename MI0 into MI.
    (* [comment removed for export] *)
    pose proof (munch_refl [(lo, bv_unsigned sp); (TH + 3168, TH + 3169)] x5) as MU5. pose proof (wmono_refl asegs x5) as WM5.
    (* [comment removed for export] *)
    step. step. if_cases K.
    { exfalso. rewrite (Z.shiftr_div_pow2 _ 47), Z.div_small in K by lia. revert K. vm_compute. discriminate. }
    clear K.
    (* [comment removed for export] *)
    step. step. step.
    assert (Q15 : 0 <= bv_unsigned a0 ≫ 32 < 2^15).
    { rewrite (Z.shiftr_div_pow2 _ 32) by lia. clear - A0R P47; try acb. split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]. }
    match goal with |- context [Z_to_bv 64 (6994688 + ?x)] =>
      replace x with (8 * (bv_unsigned a0 ≫ 32)) by (rewrite unsigned_lit, Z.shiftl_mul_pow2 by lia; lia) end.
    destruct IA1 as (IAa & IAb & IAc). unfold AIAINST in IAa, IAb, IAc.
    pose proof (ia_probe_read _ _ (8 * (bv_unsigned a0 ≫ 32) + 8) IAa ltac:(hci; lia) ltac:(hci; rewrite Z2Nat.id; lia)) as HR.
    step. clear HR. step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    assert (IAh : True -> ia_after x5) by (intros _; exact (conj IAa (conj IAb IAc))). clear IAa IAb IAc.
    (* [comment removed for export] *)
    step. step. step. step. step. st1. step. st1.
    (* [comment removed for export] *)
    pose proof (i_mcs _ _ _ _ _ _ _ _ (ienv_now_fpre _ ENV MU WM)) as Emcs.
    step. callD malloc_context_size_spec. all: try eassumption.
    step. step. if_cases K; [| exfalso; revert K; vm_compute; discriminate]. clear K.
    (* [comment removed for export] *)
    step. step. step.
    pose proof (i_got _ _ _ _ _ _ _ _ (ienv_now_fpre _ ENV MU WM)) as Egot. unfold AGOT_VALS in Egot. cbn [map] in Egot. unfold wz in Egot.
    pose proof (i_cfu _ _ _ _ _ _ _ _ (ienv_now_fpre _ ENV MU WM)) as Ecfu. replace (7586856 + 34) with 7586890 in Ecfu by reflexivity.
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
    lazymatch goal with H : mem_inv asegs ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) => rename H into MIx end.
    try clear MI. rename MIx into MI.
    lazymatch goal with H : stk asegs _ lo _ |- _ => rename H into ST end.
    (* [comment removed for export] *)
    apply rw_cells_C8_zero_split in F1.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in F1. destruct F1 as [SZC PAD]. cbn [cells_size csize Nat.add] in PAD.
    replace (bv_unsigned sp + -2120 + Z.of_nat 4) with (bv_unsigned sp + -2116) in PAD by lia.
    change 2040%nat with (8 * 255)%nat in F2. destruct (u64arr_of_junk _ _ 255 _ F2) as (buf & BUF & LBUF). clear F2.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (REC : rw_cells asegs mm (bv_unsigned sp + -16) [C8 (wz (bv_unsigned s0)); C8 (wz (bv_unsigned ra))]) end.
    { unfold wz. rewrite !Z_to_bv_bv_unsigned.
      apply (proj1 (rw_cells_app asegs _ _ [CB 8 _; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1] [C8 s0; C8 ra])) in F4.
      destruct F4 as [_ R]. cbn [cells_size csize Nat.add] in R.
      replace (bv_unsigned sp + -64 + Z.of_nat 48) with (bv_unsigned sp + -16) in R by lia. exact R. }
    assert (BELOW : goodframe (bv_unsigned sp) (bv_unsigned s0) TOP = true -> goodframe BOT (bv_unsigned sp) TOP = true -> below W (bv_unsigned s0 - 16)).
    { intros G2 G1. destruct (FCH G1 G2) as [LE _]. unfold W, below. intros l h Hin.
      cbn [In] in Hin. clear - Hin LE HI BND; try acb.
      repeat (destruct Hin as [E|Hin]; [injection E; intros; subst; lia|]). destruct Hin. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (FCH2 : goodframe BOT (bv_unsigned sp) TOP = true -> frame_chain asegs mm TOP (bv_unsigned sp) CHI) end.
    { intros G1. unfold CHI, icpt_chain.
      destruct (Sumbool.sumbool_of_bool (goodframe (bv_unsigned sp) (bv_unsigned s0) TOP)) as [G2|G2]; rewrite G2.
      - destruct (FCH G1 G2) as [LE FC]. apply fc_link; [exact REC| lia| lia| exact G2|].
        eapply frame_chain_transport; [exact FC| apply BELOW; assumption| exact MU| exact WM].
      - apply fc_last; [exact REC| lia| lia| exact G2]. }
    clear BELOW REC.
    (* [comment removed for export] *)
    pose proof (ienv_now_fpre _ ENV MU WM) as E.
    pose proof (i_got _ _ _ _ _ _ _ _ E) as Egot. unfold AGOT_VALS in Egot. cbn [map] in Egot.
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in Egot. destruct Egot as [GOTC _].
    pose proof (i_psc _ _ _ _ _ _ _ _ E) as PGC. pose proof (i_init _ _ _ _ _ _ _ _ E) as AI.
    pose proof (i_tsdi _ _ _ _ _ _ _ _ E) as TK. apply (proj1 (rw_cells_app asegs _ _ [_] _)) in TK. destruct TK as [TKI TK].
    apply (proj1 (rw_cells_app asegs _ _ [_] _)) in TK. destruct TK as [_ TKK]. cbn [cells_size csize length Nat.add] in TKK.
    replace (6988128 + Z.of_nat 1 + Z.of_nat 3) with 6988132 in TKK by reflexivity.
    pose proof (i_tp _ _ _ _ _ _ _ _ E) as TPC. pose proof (i_tsd _ _ _ _ _ _ _ _ E) as TSDC. pose proof (i_ctx _ _ _ _ _ _ _ _ E) as CTXC.
    pose proof (i_stk _ _ _ _ _ _ _ _ E) as TC. pose proof (i_t40 _ _ _ _ _ _ _ _ E) as T40. clear E. unfold wz in *.
    (* [comment removed for export] *)
    step.
    match goal with |- context [TNode (TNode TEmpty (Some (Z_to_bv 64 ?x)) TEmpty) (Some sp) (TNode TEmpty (Some ?y) TEmpty)] =>
      replace (TNode (TNode TEmpty (Some (Z_to_bv 64 x)) TEmpty) (Some sp) (TNode TEmpty (Some y) TEmpty))
         with (TNode (TNode TEmpty (Some (Z_to_bv 64 x)) TEmpty) (Some (Z_to_bv 64 (bv_unsigned sp))) (TNode TEmpty (Some y) TEmpty))
           by (rewrite Z_to_bv_bv_unsigned; reflexivity) end.
    lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
      eapply evt_cut; [ eapply (unwindimpl_spec _ _ gp tp _ _ _ _ _ _ _ _ _ _ _ _ F fc (bv_unsigned sp + -2128) 255 lo 7578528 1831612
                                 (bv_unsigned sp) TOP BOT 30 buf mm TSD CTX TH) | post_callUI segs mm ] end.
    all: unfold KPAGE, AIMG_LO, AIMG_TOP, OFF_UNWINDING, GOT_PAGESIZECACHED, ASAN_INITED, TSD_KEY_INITED, TSD_KEY, wz; rewrite ?unsigned_lit by lia.
    all: try eassumption. all: try (first [clear - BND HI; lia | (lia_guard; lia)]).
    all: try (match goal with TB : akobj TH 4096 |- _ => clear - TB BND HI LO end; aunf; lia).   (* [comment removed for export] *)
    all: try (replace (bv_unsigned sp + -2128 + 8) with (bv_unsigned sp + -2120) by lia; eexists; exact SZC).
    all: try (replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact BUF).
    all: try (replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) by lia; exact F3).
    clear GOTC PGC AI TKI TKK TPC TSDC CTXC TC T40 FCH2.
    lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -2128 + 8) [C4 _] |- _ => fold CHI in H; fold T in H; rename H into SZT end.
    lazymatch goal with H : u64arr asegs _ (bv_unsigned sp + -2128 + 16) _ |- _ => fold CHI in H; fold T in H; rename H into TRB end.
    lazymatch goal with H : rw_cells asegs _ (bv_unsigned sp + -2128 + 2056) _ |- _ => rename H into TFB end.
    lazymatch goal with H : rw_cells asegs _ (TH + 3168) _ |- _ => rename H into UNW' end.
    lazymatch goal with H : stk asegs _ lo (bv_unsigned sp + -2128) |- _ => rename H into ST' end.
    replace (bv_unsigned sp + -2128 + 8) with (bv_unsigned sp + -2120) in SZT by lia.
    replace (bv_unsigned sp + -2128 + 2056) with (bv_unsigned sp + -72) in TFB by lia.
    assert (NR : (1 <= length T <= 30)%nat) by (unfold T; pose proof (utrace_length 0x1bf2bc (bv_unsigned sp) TOP BOT 30 CHI ltac:(hci; lia)); lia).
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      assert (Eso : rw_cells asegs mm (bv_unsigned sp + -2128) [C8 (wz (bv_unsigned sp + -2128 + 16)); C8 (wz (Z.of_nat (length T)))]) end.
    { apply (proj2 (rw_cells_app asegs _ _ [_] [_])). split; [unfold wz; replace (bv_unsigned sp + -2128 + 16) with (bv_unsigned sp + -2112) by lia; exact F0|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -2128 + Z.of_nat 8) with (bv_unsigned sp + -2120) by lia.
      apply rw_cells_C4C4_C8; [clear - NR; try acb; lia|]. apply (proj2 (rw_cells_app asegs _ _ [_] [_])). split; [exact SZT|].
      cbn [cells_size csize Nat.add]. replace (bv_unsigned sp + -2120 + Z.of_nat 4) with (bv_unsigned sp + -2116) by lia. exact PAD. }
    clear F0 SZT PAD.
    (* [comment removed for export] *)
    step. step. step. step. step.
    (* [comment removed for export] *)
    step. step. step. step. step. step. step. step. step. step.
    (* [comment removed for export] *)
    assert (TRNG : Forall (fun x => 0 <= x < 2^64) T).
    { unfold T. apply utrace_range'; [| lia]. intros G1. unfold CHI, icpt_chain.
      destruct (Sumbool.sumbool_of_bool (goodframe (bv_unsigned sp) (bv_unsigned s0) TOP)) as [G2|G2]; rewrite G2.
      - constructor; [cbn [fst]; lia|]. destruct (FCH G1 G2) as [_ FC]. eapply frame_chain_ranges. exact FC.
      - constructor; [cbn [fst]; lia| constructor]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (DEPOT_transport asegs d _ mm) in DEP; [| exact MU | exact WM | solve_depot_avoid] end.
    pose proof (ienv_now_fpre _ ENV MU WM) as ENV'.
    unfold wz in TFB; rewrite ?Z_to_bv_bv_unsigned in TFB.
    pose proof (FLGh I) as FLG. eapply rw_cells_transport in FLG; [| exact MU5| exact WM5| cbn [disjoint_from cells_size csize length Nat.add Nat.mul]; lia].
    pose proof (ia_if_transport true _ _ _ (IAh I) MU5 WM5 ltac:(hci; cbn [disjoint_from]; region_decide)) as IA'. cbn in IA'. clear FLGh IAh MU5 WM5.
    apply evt_done. unfold PREPOST, free_pre_post, wz, AINST, AIAINIT. rewrite ?Z_to_bv_bv_unsigned.
    do 9 eexists. exists jk3, (drop (length T) buf). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [lazymatch goal with H : mem_inv asegs _ |- _ => exact H end|]. split; [exact ENV'|].
    split; [exact ST'|]. split; [exact Eso|]. split; [exact TRB|]. split; [rewrite length_drop, LBUF; reflexivity|].
    split; [exact TFB|]. split; [exact F4|]. split; [exact UNW'|]. split; [exact DEP|]. split; [exact TRNG|]. split; [exact NR|].
    split; [exact FLG| exact IA'].
  Qed.
End Pre.

