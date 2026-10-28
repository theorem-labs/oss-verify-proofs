(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil BCells BStep BSegs BsShadow.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac WalkTac StoreOk MemSplit Hoare RefMemcpyLib LibIface SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HEmpS.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_RwKit.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition E_BB : Z := 0xf520c.
Definition E_LP : Z := 0xf52c0.
Definition E_LM : Z := 0xf5354.
Definition E_NF : Z := 0xf53e0.
Definition E_FOUND : Z := 0xf58c4.
Definition E_STOPS : list Z := [E_BB; E_LP; E_LM; E_NF; E_FOUND].

Definition non_argN : list reg :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 15; 16; 17; 18; 20; 21; 22; 24; 25; 27; 28; 29; 30; 31]%bv.
Definition aonlyN (R R' : bvmap 5 word) : Prop := forall r, In r non_argN -> getr R' r = getr R r.
Lemma aonlyN_trans : forall R1 R2 R3, aonlyN R1 R2 -> aonlyN R2 R3 -> aonlyN R1 R3.
Proof. intros R1 R2 R3 A B r Hr. rewrite (B r Hr). apply A, Hr. Qed.
Ltac aonly_same HR HR' :=
  let r := fresh "r" in let Hr := fresh "Hr" in
  intros r Hr; refine (LbB_HEmpS.syms_same_sound _ _ _ _ _ non_argN HR HR' _ r Hr); vm_cast_no_check (@eq_refl bool true).
Ltac in_tac := unfold non_argN; cbn [In]; repeat first [ left; reflexivity | right ].

Ltac seedN :=
  apply regs_ok_srs; [apply regs_ok_seed|];
  repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | evs; assumption] |]); apply Forall_nil.
Ltac sc_rdN H :=
  eapply (sc_read_cellw _ _ _ _ _ _ _ _ H);
  [ cbn; lia
  | evs; rewrite ?w_mul_u, ?w_add_u; rewrite ?v_addi_Z by lia; first [ reflexivity | f_equal; lia ]
  | evs; first [ reflexivity | f_equal; lia ] ].
Ltac sc_brN :=
  cbn [sc_denot]; evs; rewrite ?w_remu, ?w_and by lia;
  rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu, ?br_eq_sxw, ?br_ne_sxw by lia; bool_lia.
Ltac scN :=
  lazymatch goal with
  | |- sc_denot _ _ _ (SCFlat (SA (EAlu ALU_SRL _ (ELit 3)) _) _) => sc_shdj
  | |- sc_denot _ _ _ (SCFlat _ _) => sc_adB
  | |- sc_denot _ _ _ (SCReadBase _ _ true _) => match goal with H : cellw _ _ _ 4%N _ |- _ => sc_rd_sx H end
  | |- sc_denot _ _ _ (SCReadBase _ _ false _) => match goal with H : cellw _ _ _ _ _ |- _ => sc_rdN H end
  | |- sc_denot _ _ _ (SCBr _ _ _ _) => first [ sc_brN | sc_brB | sc_caseB ]
  end.

Section NtS.
  Context {fx : FPState}.
  Context {AC : AllocCeiling}.
  Variable L : Layout.
  Variable MI : MallocIface ASEGS L.
  Variable rom : word -> option byte.
  Variables (A : AS MI) (M : mem) (S1 obj bl bc key v408 v624 : Z) (ents : list (Z * (Z * (Z * Z * Z)))).

  #[local] Abbreviation st R pc M := (@mkst fx R (Z_to_bv 64 pc) M rom).

  Definition SENV : Prop :=
    umapx MI 32 (nval32 ASEGS) A M obj bl bc ents /\ 0 <= key < 2 ^ 32
    /\ gz M obj 40 /\ (bc <> 0 -> gz M bl (8 * bc)) /\ (forall p k v, In (p, (k, v)) ents -> gz M p 32)
    /\ rw_cells asegs M (S1 + 616) [C8 (Z_to_bv 64 SHBASE)] /\ rw_cells asegs M (S1 + 408) [C8 (Z_to_bv 64 v408)]
    /\ rw_cells asegs M (S1 + 624) [C8 (Z_to_bv 64 v624)] /\ 0 <= v408 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64
    /\ 2 ^ 45 <= S1 /\ S1 + 672 <= 2 ^ 47.

  Lemma senv_bc : SENV -> 0 <= bc <= 26339969.
  Proof.
    intros [U _].
    assert (HB : forall x, In x BSEQ -> 0 <= x <= 26339969).
    { intros x Hx. unfold BSEQ in Hx. repeat (destruct Hx as [<-|Hx]; [lia|]). destruct Hx. }
    exact (HB bc (u_bseq U)).
  Qed.

  Definition efound (r : Z) : Prop := exists v, In (r, (key, v)) ents.

  Definition atE (R R' : bvmap 5 word) : Prop := aonlyN R R'.

  Definition srB : list expr :=
    srs sr_id [(2%bv, EVar 37); (9%bv, EVar 37); (17%bv, EAlu ALU_SRL (EVar 32) (ELit 3)); (16%bv, EVar 32);
               (18%bv, EVar 33); (27%bv, EVar 34); (22%bv, EVar 35); (11%bv, EVar 36)].
  Definition KB : list kentry :=
    [KWord (SA (EVar 37) 616) 8 (ELit SHBASE); KWord (SA (EVar 37) 408) 8 (EVar 38); KWord (SA (EVar 37) 624) 8 (EVar 39)].
  Definition KNBx (scr : scripts) : list kentry := kn_fix 20 E_STOPS scr E_BB srB KB 50.
  Definition SCR_B_b0 := SCR [true; true; true; true; true] [EVar 40; EVar 41; EVar 42] [].
  Definition SCR_B_q0 := SCR [true; true; true; true; false; true; true] [EVar 40; EVar 41; EVar 42] [].
  Definition SCR_B_m := SCR [true; true; true; true; false; true; false; true] [EVar 40; EVar 41; EVar 42] [].
  Definition SCR_B_p := SCR [true; true; true; true; false; true; false; false] [EVar 40; EVar 41; EVar 42] [].

  Definition atLoopM (R R' : bvmap 5 word) (q : Z) : Prop :=
    aonlyN R R' /\ getr R' 23%bv = Z_to_bv 64 q /\ getr R' 11%bv = sxw key
    /\ getr R' 19%bv = Z_to_bv 64 v624 /\ getr R' 26%bv = Z_to_bv 64 v408.
  Definition atLoopP (R R' : bvmap 5 word) (q : Z) : Prop :=
    aonlyN R R' /\ getr R' 23%bv = Z_to_bv 64 q /\ getr R' 11%bv = Z_to_bv 64 (bc - 1) /\ getr R' 12%bv = sxw key
    /\ getr R' 19%bv = Z_to_bv 64 v624 /\ getr R' 26%bv = Z_to_bv 64 v408.

  Ltac runB R vals scr :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    pose (E := Eseed R vals);
    assert (HR : regs_ok E srB R) by seedN;
    assert (HK : know_ok ASEGS E M (KNBx scr)) by
      (kn_eval; unfold know_ok;
       apply Forall_cons; [match goal with W : rw_cells _ M (_ + 616) _ |- _ => kword_cell W 0%nat (C8 (Z_to_bv 64 SHBASE)) end |];
       apply Forall_cons; [match goal with W : rw_cells _ M (_ + 408) _ |- _ => kword_cell W 0%nat (C8 (Z_to_bv 64 v408)) end |];
       apply Forall_cons; [match goal with W : rw_cells _ M (_ + 624) _ |- _ => kword_cell W 0%nat (C8 (Z_to_bv 64 v624)) end |];
       know_tac);
    xrun HR HK 100%nat E_STOPS scr 50%N; [ split_scs; scN | ].

  Lemma emp_blkB : forall R (pw b q0 : Z), SENV ->
    getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 -> getr R 18%bv = Z_to_bv 64 key ->
    getr R 17%bv = Z_to_bv 64 (obj / 8) -> getr R 16%bv = Z_to_bv 64 obj -> getr R 27%bv = Z_to_bv 64 bc ->
    getr R 22%bv = Z_to_bv 64 (hmod key bc) -> getr R 11%bv = Z_to_bv 64 pw -> 0 <= pw < 2 ^ 64 -> bc <> 0 ->
    cell8 ASEGS M (bl + 8 * hmod key bc) b -> 0 <= b -> b + 8 <= 2 ^ 47 -> b mod 8 = 0 ->
    (b <> 0 -> cell8 ASEGS M b q0) -> (b <> 0 -> gz M b 8) ->
    exists R',
      ((b = 0 \/ q0 = 0) /\ msteps ASEGS (st R E_BB M) (st R' E_NF M) /\ aonlyN R R')
      \/ (b <> 0 /\ q0 <> 0 /\ 2 <= pw /\ msteps ASEGS (st R E_BB M) (st R' E_LM M) /\ atLoopM R R' q0)
      \/ (b <> 0 /\ q0 <> 0 /\ pw < 2 /\ msteps ASEGS (st R E_BB M) (st R' E_LP M) /\ atLoopP R R' q0).
  Proof.
    intros R pw b q0 HS H2 H9 H18 H17 H16 H27 H22 H11 Hpw Hbc Hb Hb0 Hb1 Hbal Hq0 Hgb.
    pose proof (senv_bc HS) as Hbcr.
    destruct HS as (U & Hkey & Gobj & Gbl & _ & W616 & W408 & W624 & Hv408 & Hv624 & HS1a & HS1b).
    specialize (Gbl Hbc).
    pose proof (u_obj_al U) as Hoa. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    pose proof (u_bl_al U) as Hbla. pose proof (u_bl_lo U Hbc) as Hbl0. pose proof (u_bl_hi U) as Hbl1.
    assert (Hidx : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia).
    assert (H17' : getr R 17%bv = alu64 ALU_SRL (Z_to_bv 64 obj) (Z_to_bv 64 3))
      by (rewrite H17, LbB_HEmpS.srl3_val by lia; reflexivity).
    destruct (u_hdr U) as [Hblc _ _ _ _ _].
    clear H17 U.
    unfold cell8 in Hb, Hblc. pose proof (proj1 Hb) as Hbr.
    destruct (Z.eq_dec b 0) as [Hbz|Hbnz].
    - runB R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 pw; Z_to_bv 64 S1;
              Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0] SCR_B_b0.
      exists R'. left. split; [left; exact Hbz|]. split; [exact Hms | aonly_same HR HR'].
    - specialize (Hq0 Hbnz). specialize (Hgb Hbnz). unfold cell8 in Hq0. pose proof (proj1 Hq0) as Hq0r.
      destruct (Z.eq_dec q0 0) as [Hqz|Hqnz].
      + runB R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 pw; Z_to_bv 64 S1;
                Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0] SCR_B_q0.
        exists R'. left. split; [right; exact Hqz|]. split; [exact Hms | aonly_same HR HR'].
      + destruct (Z_le_gt_dec 2 pw) as [Hw|Hw].
        * runB R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 pw; Z_to_bv 64 S1;
                  Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0] SCR_B_m.
          exists R'. right; left. split; [exact Hbnz|]. split; [exact Hqnz|]. split; [exact Hw|]. split; [exact Hms|].
          rreg HR' 23%bv G23. rreg HR' 11%bv G11. rreg HR' 19%bv G19. rreg HR' 26%bv G26.
          split; [aonly_same HR HR'|]. split; [exact G23|]. split; [rewrite G11; apply sextw_val; lia|].
          split; [exact G19 | exact G26].
        * runB R [Z_to_bv 64 obj; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 pw; Z_to_bv 64 S1;
                  Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 bl; Z_to_bv 64 b; Z_to_bv 64 q0] SCR_B_p.
          exists R'. right; right. split; [exact Hbnz|]. split; [exact Hqnz|]. split; [lia|]. split; [exact Hms|].
          rreg HR' 23%bv G23. rreg HR' 11%bv G11. rreg HR' 12%bv G12. rreg HR' 19%bv G19. rreg HR' 26%bv G26.
          split; [aonly_same HR HR'|]. split; [exact G23|]. split; [rewrite G11; apply w_addm; lia|].
          split; [rewrite G12; apply sextw_val; lia|]. split; [exact G19 | exact G26].
  Qed.

  Definition srLM : list expr :=
    srs sr_id [(23%bv, EVar 32); (11%bv, EVar 33); (2%bv, EVar 37); (9%bv, EVar 37); (18%bv, EVar 34); (27%bv, EVar 35);
               (22%bv, EVar 36); (19%bv, EVar 39); (26%bv, EVar 38)].
  Definition srLP : list expr :=
    srs sr_id [(23%bv, EVar 32); (11%bv, EVar 42); (12%bv, EVar 33); (2%bv, EVar 37); (9%bv, EVar 37); (18%bv, EVar 34);
               (27%bv, EVar 35); (22%bv, EVar 36); (19%bv, EVar 39); (26%bv, EVar 38)].
  Definition KL : list kentry := [KWord (SA (EVar 37) 616) 8 (ELit SHBASE)].
  Definition KNL (pc : Z) (sr : list expr) (scr : scripts) : list kentry := kn_fix 20 E_STOPS scr pc sr KL 50.
  Definition SCR_P_f := SCR [true; false; false] [EVar 40; EVar 41] [].
  Definition SCR_P_nf := SCR [true; true; true] [EVar 40; EVar 41] [].
  Definition SCR_P_nx := SCR [true; true; false; true] [EVar 40; EVar 41] [].
  Definition SCR_P_end := SCR [true; true; false; false] [EVar 40; EVar 41] [].
  Definition SCR_M_f := SCR [true; false; false] [EVar 40; EVar 41] [].
  Definition SCR_M_nf (lt : bool) := SCR [true; true; lt; true] [EVar 40; EVar 41] [].
  Definition SCR_M_nx (lt : bool) := SCR [true; true; lt; false; true] [EVar 40; EVar 41] [].
  Definition SCR_M_end (lt : bool) := SCR [true; true; lt; false; false] [EVar 40; EVar 41] [].

  Lemma node_factsE : forall l1 p k v l2, SENV -> ents = l1 ++ (p, (k, v)) :: l2 ->
    0 < p /\ p + 32 <= 2 ^ 47 /\ cell8 ASEGS M (p + 8) k /\ cell4 ASEGS M (p + 16) k /\ 0 <= k < 2 ^ 32
    /\ cell8 ASEGS M p (hdaddr l2) /\ gz M p 32 /\ p mod 16 = 0.
  Proof.
    intros l1 p k v l2 HS He.
    destruct HS as (U & _ & _ & _ & Gn & _).
    assert (Hin : In (p, (k, v)) ents) by (rewrite He; apply in_app_iff; right; left; reflexivity).
    destruct (u_node U p k v Hin) as (_ & Hp0 & Hp1 & Hal & Hh & Hk & Hkr & _).
    assert (Hc : chain ASEGS M (l1 ++ (p, (k, v)) :: l2)) by (rewrite <- He; exact (u_chain U)).
    assert (Hn : cell8 ASEGS M p (hdaddr l2)).
    { clear - Hc. induction l1 as [|[q kv] l1 IH]; cbn in Hc; [exact (proj1 Hc) | exact (IH (proj2 Hc))]. }
    split; [lia|]. split; [lia|]. split; [exact Hh|]. split; [exact Hk|]. split; [lia|]. split; [exact Hn|].
    split; [exact (Gn p k v Hin) | exact Hal].
  Qed.

  Definition loop_res (R : bvmap 5 word) (pc : Z) : Prop :=
    exists R', (exists r, efound r /\ msteps ASEGS (st R pc M) (st R' E_FOUND M) /\ aonlyN R R' /\ getr R' 23%bv = Z_to_bv 64 r
                          /\ getr R' 19%bv = Z_to_bv 64 v624 /\ getr R' 26%bv = Z_to_bv 64 v408)
               \/ (msteps ASEGS (st R pc M) (st R' E_NF M) /\ aonlyN R R').

  Lemma loop_res_cons : forall R R1 pc pc1, msteps ASEGS (st R pc M) (st R1 pc1 M) -> aonlyN R R1 -> loop_res R1 pc1 -> loop_res R pc.
  Proof.
    intros R R1 pc pc1 Hms AO [R' [(r & Ef & Hms' & AO' & G23 & G19 & G26) | (Hms' & AO')]].
    - exists R'. left. exists r. split; [exact Ef|]. split; [exact (CatSim.msteps_trans _ _ _ _ Hms Hms')|].
      split; [exact (aonlyN_trans _ _ _ AO AO')|]. split; [exact G23|]. split; [exact G19 | exact G26].
    - exists R'. right. split; [exact (CatSim.msteps_trans _ _ _ _ Hms Hms') | exact (aonlyN_trans _ _ _ AO AO')].
  Qed.

  Ltac runL R vals sr scr pc :=
    let E := fresh "E" in let HR := fresh "HR" in let HK := fresh "HK" in
    try unfold loop_res;
    pose (E := Eseed R vals);
    assert (HR : regs_ok E sr R) by seedN;
    assert (HK : know_ok ASEGS E M (KNL pc sr scr)) by
      (kn_eval; unfold know_ok;
       apply Forall_cons; [match goal with W : rw_cells _ M (_ + 616) _ |- _ => kword_cell W 0%nat (C8 (Z_to_bv 64 SHBASE)) end |];
       know_tac);
    xrun HR HK 100%nat E_STOPS scr 50%N; [ split_scs; scN | ].

  Ltac finL_nf :=
    lazymatch goal with
    | HR : regs_ok _ _ ?R0, HR' : regs_ok _ _ ?R1, Hms : msteps _ _ (mkst ?R1 _ _ _) |- _ =>
        exists R1; right; split; [exact Hms | aonly_same HR HR']
    end.

  Ltac finL_found p v He :=
    lazymatch goal with
    | HR : regs_ok _ _ ?R0, HR' : regs_ok _ _ ?R1, Hms : msteps _ _ (mkst ?R1 _ _ _) |- _ =>
        exists R1; left; exists p;
        split; [exists v; rewrite He; apply in_app_iff; right; left; reflexivity|];
        split; [exact Hms|]; split; [aonly_same HR HR'|];
        split; [let G := fresh in rreg HR' 23%bv G; exact G|];
        split; [let G := fresh in rreg HR' 19%bv G; exact G | let G := fresh in rreg HR' 26%bv G; exact G]
    end.

  Ltac finL_next pc IH l1' p' k' v' HS He' :=
    lazymatch goal with
    | HR : regs_ok _ _ ?R0, HR' : regs_ok _ _ ?R1, Hms : msteps _ _ (mkst ?R1 _ _ _) |- _ =>
        refine (loop_res_cons R0 R1 pc pc Hms _ _); [aonly_same HR HR'|];
        apply (IH l1' p' k' v' R1 HS He'); try assumption;
        first [ let G := fresh in rreg HR' 23%bv G; exact G | let G := fresh in rreg HR' 11%bv G; exact G
              | let G := fresh in rreg HR' 12%bv G; exact G | let G := fresh in rreg HR' 2%bv G; exact G
              | let G := fresh in rreg HR' 9%bv G; exact G | let G := fresh in rreg HR' 18%bv G; exact G
              | let G := fresh in rreg HR' 27%bv G; exact G | let G := fresh in rreg HR' 22%bv G; exact G
              | let G := fresh in rreg HR' 19%bv G; exact G | let G := fresh in rreg HR' 26%bv G; exact G ]
    end.

  Lemma loopM : forall l2 l1 p k v R, SENV ->
    ents = l1 ++ (p, (k, v)) :: l2 -> bc <> 0 ->
    getr R 23%bv = Z_to_bv 64 p -> getr R 11%bv = sxw key -> getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 ->
    getr R 18%bv = Z_to_bv 64 key -> getr R 27%bv = Z_to_bv 64 bc -> getr R 22%bv = Z_to_bv 64 (hmod key bc) ->
    getr R 19%bv = Z_to_bv 64 v624 -> getr R 26%bv = Z_to_bv 64 v408 ->
    loop_res R E_LM.
  Proof.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R HS He Hbc H23 H11 H2 H9 H18 H27 H22 H19 H26;
      pose proof (senv_bc HS) as Hbcr;
      destruct (node_factsE l1 p k v _ HS He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx & Gp & Hal);
      pose proof HS as HS';
      destruct HS' as (_ & Hkey & _ & _ & _ & W616 & _ & _ & Hv408 & Hv624 & HS1a & HS1b);
      cbn [hdaddr] in Hnx; unfold cell8 in Hh, Hnx; unfold cell4 in Hk;
      assert (Hidx : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia);
      pose proof (Z.mod_pos_bound k bc ltac:(lia)) as Hmk.
    - destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 key; sxw key] srLM SCR_M_f E_LM.
        finL_found p v He.
      + destruct (Z.ltb_spec k bc) as [Hlt|Hge].
        * destruct (Z.eq_dec k (hmod key bc)) as [Hc|Hc].
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 0] srLM (SCR_M_end true) E_LM.
             finL_nf.
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 0] srLM (SCR_M_nf true) E_LM.
             finL_nf.
        * destruct (Z.eq_dec (k mod bc) (hmod key bc)) as [Hc|Hc].
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 0] srLM (SCR_M_end false) E_LM.
             finL_nf.
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 0] srLM (SCR_M_nf false) E_LM.
             finL_nf.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_factsE _ p' k' v' _ HS He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 key; sxw key] srLM SCR_M_f E_LM.
        finL_found p v He.
      + destruct (Z.ltb_spec k bc) as [Hlt|Hge].
        * destruct (Z.eq_dec k (hmod key bc)) as [Hc|Hc].
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 p'] srLM (SCR_M_nx true) E_LM.
             finL_next E_LM IH (l1 ++ [(p, (k, v))]) p' k' v' HS He'.
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 p'] srLM (SCR_M_nf true) E_LM.
             finL_nf.
        * destruct (Z.eq_dec (k mod bc) (hmod key bc)) as [Hc|Hc].
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 p'] srLM (SCR_M_nx false) E_LM.
             finL_next E_LM IH (l1 ++ [(p, (k, v))]) p' k' v' HS He'.
          -- runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                     Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 p'] srLM (SCR_M_nf false) E_LM.
             finL_nf.
  Qed.

  Lemma loopP : forall l2 l1 p k v R, SENV ->
    ents = l1 ++ (p, (k, v)) :: l2 -> bc = 2 ->
    getr R 23%bv = Z_to_bv 64 p -> getr R 11%bv = Z_to_bv 64 (bc - 1) -> getr R 12%bv = sxw key ->
    getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 -> getr R 18%bv = Z_to_bv 64 key -> getr R 27%bv = Z_to_bv 64 bc ->
    getr R 22%bv = Z_to_bv 64 (hmod key bc) -> getr R 19%bv = Z_to_bv 64 v624 -> getr R 26%bv = Z_to_bv 64 v408 ->
    loop_res R E_LP.
  Proof.
    induction l2 as [|[p' [k' v']] l2' IH]; intros l1 p k v R HS He Hbc2 H23 H11 H12 H2 H9 H18 H27 H22 H19 H26;
      destruct (node_factsE l1 p k v _ HS He) as (Hp0 & Hp1 & Hh & Hk & Hkr & Hnx & Gp & Hal);
      pose proof HS as HS';
      destruct HS' as (_ & Hkey & _ & _ & _ & W616 & _ & _ & Hv408 & Hv624 & HS1a & HS1b);
      cbn [hdaddr] in Hnx; unfold cell8 in Hh, Hnx; unfold cell4 in Hk;
      assert (Hidx : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia);
      assert (Hland : 0 <= Z.land k (bc - 1) < 2 ^ 64)
        by (rewrite Hbc2; change (2 - 1) with (Z.ones 1); rewrite Z.land_ones by lia;
            pose proof (Z.mod_pos_bound k (2 ^ 1) ltac:(lia)); lia).
    - destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 key; sxw key; Z_to_bv 64 (bc - 1)] srLP SCR_P_f E_LP.
        finL_found p v He.
      + destruct (Z.eq_dec (Z.land k (bc - 1)) (hmod key bc)) as [Hc|Hc].
        * runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                  Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 (bc - 1)] srLP SCR_P_end E_LP.
          finL_nf.
        * runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                  Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 0; Z_to_bv 64 (bc - 1)] srLP SCR_P_nf E_LP.
          finL_nf.
    - assert (He' : ents = (l1 ++ [(p, (k, v))]) ++ (p', (k', v')) :: l2') by (rewrite He, <- app_assoc; reflexivity).
      destruct (node_factsE _ p' k' v' _ HS He') as (Hp0' & Hp1' & _).
      destruct (Z.eq_dec k key) as [->|Hne].
      + runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 key; sxw key; Z_to_bv 64 (bc - 1)] srLP SCR_P_f E_LP.
        finL_found p v He.
      + destruct (Z.eq_dec (Z.land k (bc - 1)) (hmod key bc)) as [Hc|Hc].
        * runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                  Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 p'; Z_to_bv 64 (bc - 1)] srLP SCR_P_nx E_LP.
          finL_next E_LP IH (l1 ++ [(p, (k, v))]) p' k' v' HS He'.
        * runL R [Z_to_bv 64 p; sxw key; Z_to_bv 64 key; Z_to_bv 64 bc; Z_to_bv 64 (hmod key bc); Z_to_bv 64 S1;
                  Z_to_bv 64 v408; Z_to_bv 64 v624; Z_to_bv 64 k; Z_to_bv 64 p'; Z_to_bv 64 (bc - 1)] srLP SCR_P_nf E_LP.
          finL_nf.
  Qed.

  Lemma emp_from_bb : forall R (pw : Z), SENV -> bc <> 0 ->
    getr R 2%bv = Z_to_bv 64 S1 -> getr R 9%bv = Z_to_bv 64 S1 -> getr R 18%bv = Z_to_bv 64 key ->
    getr R 17%bv = Z_to_bv 64 (obj / 8) -> getr R 16%bv = Z_to_bv 64 obj -> getr R 27%bv = Z_to_bv 64 bc ->
    getr R 22%bv = Z_to_bv 64 (hmod key bc) ->
    getr R 11%bv = Z_to_bv 64 pw -> 0 <= pw < 2 ^ 64 -> (bc <> 2 -> 2 <= pw) -> (bc = 2 -> pw < 2) ->
    loop_res R E_BB.
  Proof.
    intros R pw HS Hbc H2 H9 H18 H17 H16 H27 H22 H11 Hpw Hpw2 Hpw1.
    pose proof (senv_bc HS) as Hbcr.
    pose proof HS as HS'.
    destruct HS' as (U & Hkey & Gobj & _ & Gn & _).
    assert (Hidx : 0 <= hmod key bc < bc) by (unfold hmod; apply Z.mod_pos_bound; lia).
    pose proof (u_obj_al U) as Hoa. pose proof (u_obj_lo U) as Ho0. pose proof (u_obj_hi U) as Ho1.
    destruct (u_bkt U (hmod key bc) Hidx) as (b & Hb & Hbk).
    assert (HC : forall l : list (Z * (Z * (Z * Z * Z))), hdaddr l <> 0 ->
                 exists p k v l', l = (p, (k, v)) :: l' /\ hdaddr l = p).
    { intros [|[p [k v]] l'] Hl; [cbn in Hl; lia|]. exists p, k, v, l'. split; reflexivity. }
    assert (KEY : exists q0, 0 <= b /\ b + 8 <= 2 ^ 47 /\ b mod 8 = 0 /\ (b <> 0 -> cell8 ASEGS M b q0)
                  /\ (b <> 0 -> gz M b 8) /\ (q0 <> 0 -> exists l1 p k v l2, ents = l1 ++ (p, (k, v)) :: l2 /\ q0 = p)).
    { unfold bucket_ok in Hbk. destruct Hbk as [Hb0 | [Hbin | (Hbo & _ & _)]].
      - exists 0. subst b. split; [lia|]. split; [lia|]. split; [reflexivity|].
        split; [intros X; exfalso; apply X; reflexivity|]. split; [intros X; exfalso; apply X; reflexivity|].
        intros X; exfalso; apply X; reflexivity.
      - apply in_map_iff in Hbin. destruct Hbin as ([b' [kb vb]] & Hfst & Hin). cbn in Hfst. subst b'.
        destruct (in_split _ _ Hin) as (l1 & l2 & He).
        destruct (node_factsE l1 b kb vb l2 HS He) as (Hp0 & Hp1 & _ & _ & _ & Hnx & Gp & Hal).
        exists (hdaddr l2). split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
        split; [intros _; exact Hnx|]. split; [intros _ i Hi; apply Gp; lia|].
        intros Hq. destruct (HC l2 Hq) as (p' & k' & v' & l2' & -> & Hh).
        exists (l1 ++ [(b, (kb, vb))]), p', k', v', l2'. split; [rewrite He, <- app_assoc; reflexivity | exact Hh].
      - subst b. destruct (u_hdr U) as [_ _ Hp1c _ _ _].
        exists (hdaddr ents). split; [lia|]. split; [lia|]. split; [Z.div_mod_to_equations; lia|].
        split; [intros _; exact Hp1c|].
        split; [intros _ i Hi; replace (obj + 16 + i) with (obj + (16 + i)) by lia; apply Gobj; lia|].
        intros Hq. destruct (HC ents Hq) as (p & k & v & l' & He & Hh).
        exists [], p, k, v, l'. split; [exact He | exact Hh]. }
    destruct KEY as (q0 & Hb0 & Hb1 & Hbal & Hq0 & Hgb & Hq).
    destruct (emp_blkB R pw b q0 HS H2 H9 H18 H17 H16 H27 H22 H11 Hpw Hbc Hb Hb0 Hb1 Hbal Hq0 Hgb)
      as (R' & [(_ & Hms & AO) | [(Hbnz & Hqnz & Hw & Hms & AO & G23 & G11 & G19 & G26)
                                 | (Hbnz & Hqnz & Hw & Hms & AO & G23 & G11 & G12 & G19 & G26)]]).
    - exists R'. right. split; [exact Hms | exact AO].
    - destruct (Hq Hqnz) as (l1 & p & k & v & l2 & He & ->).
      refine (loop_res_cons R R' E_BB E_LM Hms AO _).
      apply (loopM l2 l1 p k v R' HS He Hbc G23 G11); try assumption;
        match goal with |- getr R' ?r = _ => rewrite (AO r ltac:(in_tac)); assumption end.
    - assert (Hbc2 : bc = 2) by (destruct (Z.eq_dec bc 2) as [E2|E2]; [exact E2 | specialize (Hpw2 E2); lia]).
      destruct (Hq Hqnz) as (l1 & p & k & v & l2 & He & ->).
      refine (loop_res_cons R R' E_BB E_LP Hms AO _).
      apply (loopP l2 l1 p k v R' HS He Hbc2 G23 G11 G12); try assumption;
        match goal with |- getr R' ?r = _ => rewrite (AO r ltac:(in_tac)); assumption end.
  Qed.
End NtS.
