(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPropExec BxSymExec3 BxSymExec3Sound BxSymExec3B BothAcct BothPlanCore BothPlan BothPlanSound BothPlanSoundSums BothInit BsImages BsPlanImages BsHSTab BsStartupHSF BsMainVM BsMainState BsMainFacts BsMainLazyChk BsMainLazy BazyRestrict BazySR.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsMainSyms BerfLia.
Import ListNotations. Import AX2. Import AX2S. Import AX2B. Import APC. Import AP. Import APS. Import APSX.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Inductive csym : Type :=
  | CAbs
  | CB04 | CB05 | CB06 | CB08 | CB09 | CB10 | CB11 | CB12 | CB13 | CB16 | CB20 | CB21 | CB22 | CB23 | CB19R
  | CRI
  | CSP0
  | CSTK
  | CBRK0
  | CSH16.

Definition cx : Type := (csym * Z)%type.

Definition pgE (k : nat) : expr := EMd Instr.M_MUL (ELit 4096) (EVar k).

Definition e_sp0' : expr :=
  EAlu Instr.ALU_ADD (EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 6))) (EMd Instr.M_MUL (ELit 16) (EVar 10)).
Definition e_pg' : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 32768) (EVar 0)) (EMd Instr.M_MUL (ELit 4096) (EVar 6)).
Definition e_ri' : expr := EAlu Instr.ALU_ADD (EMd Instr.M_MUL (ELit 4096) (EVar K_B06)) (EMd Instr.M_MUL (ELit (-4096)) (EVar K_R06)).

Definition stk_up (cls : nat) : Z := match cls with 0%nat => 0 | _ => 4096 end.

Definition csym_base (g : bool) (cls : nat) (s : csym) : expr * Z :=
  match s with
  | CAbs => (ELit 0, 0)
  | CB04 => (pgE K_B04, 0) | CB05 => (pgE K_B05, 0) | CB06 => (pgE K_B06, 0) | CB08 => (pgE K_B08, 0) | CB09 => (pgE K_B09, 0)
  | CB10 => (pgE K_B10, 0) | CB11 => (pgE K_B11, 0) | CB12 => (pgE K_B12, 0) | CB13 => (pgE K_B13, 0) | CB16 => (pgE K_B16, 0)
  | CB20 => (pgE (K_B20 g), 0) | CB21 => (pgE (K_B21 g), 0) | CB22 => (pgE (K_B22 g), 0) | CB23 => (pgE (K_B23 g), 0)
  | CB19R => (if g then (ELit 0, 0) else (pgE K_META, 0))
  | CRI => (e_ri', 137439019008)
  | CSP0 => (e_sp0', 0)
  | CSTK => (e_pg', stk_up cls)
  | CBRK0 => (pgE 5, 0)
  | CSH16 => (EMd Instr.M_MUL (ELit 512) (EVar K_B16), 0x7fff8000)
  end.

Definition csym_val (sp0z brk0z : Z) (X : pm_syms) (s : csym) : Z :=
  match s with
  | CAbs => 0
  | CB04 => ps_b04 X | CB05 => ps_b05 X | CB06 => ps_b06 X | CB08 => ps_b08 X | CB09 => ps_b09 X | CB10 => ps_b10 X
  | CB11 => ps_b11 X | CB12 => ps_b12 X | CB13 => ps_b13 X | CB16 => ps_b16 X | CB20 => ps_b20 X | CB21 => ps_b21 X
  | CB22 => ps_b22 X | CB23 => ps_b23 X | CB19R => ps_b19r X
  | CRI => pm_region_info X
  | CSP0 => sp0z
  | CSTK => pm_stack_top sp0z
  | CBRK0 => brk0z
  | CSH16 => pm_sh (ps_b16 X)
  end.
Definition cx_val (sp0z brk0z : Z) (X : pm_syms) (a : cx) : Z := csym_val sp0z brk0z X (fst a) + snd a.

Definition cx_vexpr (g : bool) (cls : nat) (v : cx) : expr := let (b, k) := csym_base g cls (fst v) in EAlu Instr.ALU_ADD b (ELit (k + snd v)).

Definition lin_eqz (x y : lin) : bool :=
  Z.eqb (fst x) (fst y) && list_eqb (fun t u => Z.eqb (fst t) (fst u) && expr_eqb (snd t) (snd u)) (snd x) (snd y).
Lemma lin_eqz_eq : forall x y, lin_eqz x y = true -> x = y.
Proof.
  intros [cx tx] [cy ty] H. unfold lin_eqz in H. cbn [fst snd] in H. apply andb_prop in H as [H1 H2]. apply Z.eqb_eq in H1.
  apply list_eqb_eq in H2; [congruence|]. intros [a b] [c d] Ht. cbn [fst snd] in Ht. apply andb_prop in Ht as [Ha Hb].
  apply Z.eqb_eq in Ha. apply expr_eqb_eq in Hb. congruence.
Qed.

Definition holes : list nat := seq 0 6.

Record world : Type := WS { w_uw : option bool; w_brk : option bool }.
Definition w_all : world := WS None None.
Definition hole_short (h : nat) : bool := match h with 1%nat | 3%nat => true | _ => false end.
Definition osel (o : option bool) (b : bool) : bool := match o with None => true | Some b' => Bool.eqb b' b end.
Definition hole_sel (w : world) (h : nat) : bool := osel (w_uw w) (hole_short h) && osel (w_brk w) (hole_granted h).
Definition all_holes_w (w : world) (f : bool -> nat -> acs -> bool) : bool :=
  forallb (fun h => if hole_sel w h then match HSF_asan h with Some ch => f (hole_granted h) (hole_class h) ch | None => true end else true) holes.
Definition all_holes (f : bool -> nat -> acs -> bool) : bool := all_holes_w w_all f.

Definition world_ok (w : world) (short granted : bool) : Prop := osel (w_uw w) short = true /\ osel (w_brk w) granted = true.

Definition zero_check_w (w : world) (a : cx) (n : Z) : bool :=
  all_holes_w w (fun g cls ch => let (b, k) := csym_base g cls (fst a) in kzero_xB (mkbc (kn ch)) (kn ch) b (k + snd a) (ELit n)).
Notation zero_check := (zero_check_w w_all) (only parsing).

Definition fill1 (b : expr) (off n c : Z) (K : kentry) : bool :=
  match K with
  | KFill (SA zb zk) (ELit zn) zc => expr_eqb b zb && Z.eqb c zc && Z.leb zk off && Z.leb (off + n) (zk + zn) && Z.leb 0 zn && Z.ltb zn (2 ^ 62)
  | KZero (SA zb zk) (ELit zn) => expr_eqb b zb && Z.eqb c 0 && Z.leb zk off && Z.leb (off + n) (zk + zn) && Z.leb 0 zn && Z.ltb zn (2 ^ 62)
  | _ => false
  end.
Definition fill_check_w (w : world) (a : cx) (n c : Z) : bool :=
  all_holes_w w (fun g cls ch => let (b, k) := csym_base g cls (fst a) in existsb (fill1 b (k + snd a) n c) (kn ch)).
Notation fill_check := (fill_check_w w_all) (only parsing).

Definition ksel (b : expr) (lo hi : Z) (K : kentry) : bool :=
  match K with
  | KWord (SA kb kk) w _ => expr_eqb kb b && Z.ltb kk hi && Z.ltb lo (kk + Z.of_nat w)
  | KZero (SA kb kk) (ELit l0) | KFill (SA kb kk) (ELit l0) _ | KBlob (SA kb kk) (ELit l0) _ => expr_eqb kb b && Z.ltb kk hi && Z.ltb lo (kk + l0)
  | KImg l h => match b with ELit 0 => Z.ltb l hi && Z.ltb lo h | _ => false end
  | _ => false
  end.
Definition bytes_check_w (w : world) (a : cx) (zs : list Z) : bool :=
  all_holes_w w (fun g cls ch => let (b, k) := csym_base g cls (fst a) in
     if (match kread_bytesB ASEGS (mkbc (List.filter (ksel b (k + snd a) (k + snd a + Z.of_nat (length zs))) (kn ch))) (length zs) b (k + snd a) with
         | Some zs' => list_eqb Z.eqb zs' zs | None => false end) then true
     else match kread_bytesB ASEGS (mkbc (kn ch)) (length zs) b (k + snd a) with Some zs' => list_eqb Z.eqb zs' zs | None => false end).
Notation bytes_check := (bytes_check_w w_all) (only parsing).

Definition word_check_w (w : world) (a : cx) (v : cx) : bool :=
  all_holes_w w (fun g cls ch => let (b, k) := csym_base g cls (fst a) in
     match kread8eB ASEGS (mkbc (kn ch)) b (k + snd a) with
     | Some e => lin_eqz (lin_of e) (lin_of (cx_vexpr g cls v))
     | None => false
     end).
Notation word_check := (word_check_w w_all) (only parsing).

Definition img1 (lo hi : Z) (K : kentry) : bool := match K with KImg l h => Z.leb l lo && Z.leb hi h | _ => false end.
Definition img_check (lo hi : Z) : bool :=
  Z.leb 65536 lo && Z.leb hi 7241728 && all_holes (fun g cls ch => existsb (img1 lo hi) (kn ch)).

Ltac lia_leaf := lazymatch goal with |- _ \/ _ => fail | |- _ => lia end.
Ltac solve_disj := first [ lia_leaf | (left; solve_disj) | (right; solve_disj) ].
Ltac zsolve := repeat match goal with H : _ \/ _ |- _ => destruct H | H : False |- _ => destruct H end; solve_disj.

Ltac lia_leafT := lazymatch goal with |- _ \/ _ => fail | |- _ => solve [fastlia] end.
Ltac solve_disjT := first [ lia_leafT | (left; solve_disjT) | (right; solve_disjT) ].
Ltac zsolveT := repeat match goal with H : _ \/ _ |- _ => destruct H | H : False |- _ => destruct H end; first [solve_disjT | solve_disj].
Ltac zinP_norm2 := cbn [zinP fst snd app]; repeat (rewrite ?zinP_app, ?zinP_ifr; cbn [zinP fst snd app]).
Ltac zpinP_norm := cbn [zpinP fst snd app]; repeat (rewrite ?zpinP_app, ?zpinP_ifr; cbn [zpinP fst snd app]).

Lemma HS_some_lt : forall h ch, HSF_asan h = Some ch -> (h < 6)%nat.
Proof.
  intros h ch H. apply hs_lookup_cases in H. cbn [HSF_asan_table fold_right fst snd] in H.
  do 6 (destruct H as [[-> ->]|H]; [lia|]). destruct H.
Qed.

Definition VISK (sp0z brk0z : Z) (X : pm_syms) : list (Z * Z) := firstn 13 (VISZ0 sp0z brk0z X).
Lemma VISK_VISZ0 : forall sp0z brk0z X p, In p (VISK sp0z brk0z X) -> In p (VISZ0 sp0z brk0z X).
Proof. intros sp0z brk0z X p H. unfold VISK in H. rewrite <- (firstn_skipn 13 (VISZ0 sp0z brk0z X)). apply in_app_iff. left. exact H. Qed.

Lemma zinP_In : forall z l, zinP z l <-> exists p, In p l /\ fst p <= z < fst p + snd p.
Proof.
  intros z l. induction l as [|p l IH]; cbn [zinP In].
  - split; [tauto | intros [p [[] _]]].
  - rewrite IH. split.
    + intros [H|[q [Hq Hz]]]; [exists p; tauto | exists q; tauto].
    + intros [q [[<-|Hq] Hz]]; [left; exact Hz | right; exists q; tauto].
Qed.

Section CELLS.
  Variables (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput).
  Variables (h : nat) (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
  Hypothesis Vsp : valid_sp sp0.
  Hypothesis Vbrk : valid_brk ASEGS brk0.
  Hypothesis Vav : valid_argv (in_argv inp).
  Hypothesis Vev : valid_envp (in_envp inp).
  Hypothesis Vfit : entry_stack_fits sp0 (in_argv inp) (in_envp inp).
  Hypothesis Hh : HSF_asan h = Some ch.
  Hypothesis HC : cs_ok ASEGS ASAN_H BothInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
                        (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model.
  #[local] Notation g := (hole_granted h).
  #[local] Notation cls := (hole_class h).
  #[local] Notation MR := (Mr ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model FULL).
  #[local] Notation HID := (hid ASAN_H (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) E ch model).
  Let X := Xof g E.
  Let brk0z := bv_unsigned brk0.
  Let sp0z := bv_unsigned sp0.
  Let KNF := co_know _ _ _ _ _ _ _ _ _ _ _ HC.

  Lemma all_holes_w_here : forall w f, all_holes_w w f = true -> hole_sel w h = true -> f g cls ch = true.
  Proof.
    intros w f H Hs. unfold all_holes_w in H.
    assert (Hin : In h holes) by (unfold holes; apply in_seq; pose proof (HS_some_lt h ch Hh); lia).
    pose proof (proj1 (forallb_forall _ _) H h Hin) as H1. cbn beta in H1. rewrite Hs, Hh in H1. exact H1.
  Qed.
  Lemma hole_sel_all : hole_sel w_all h = true.
  Proof. reflexivity. Qed.
  Lemma all_holes_here : forall f, all_holes f = true -> f g cls ch = true.
  Proof. intros f H. exact (all_holes_w_here w_all f H hole_sel_all). Qed.

  Definition uw_fact (h : nat) : kentry :=
    if hole_short h then KRange (EVar 10) 6 10 else if (h <? 4)%nat then KRange (EVar 10) 0 5 else KRange (EVar 10) 11 255.
  Lemma uw_facts : forallb (fun h => match HSF_asan h with Some ch => has_fact (kn ch) (uw_fact h) | None => true end) holes = true.
  Proof. vm_compute. reflexivity. Qed.
  Lemma hole_short_pm : pm_short sp0z = hole_short h.
  Proof.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & _).
    assert (Hin : In h holes) by (unfold holes; apply in_seq; pose proof (HS_some_lt h ch Hh); lia).
    pose proof (proj1 (forallb_forall _ _) uw_facts h Hin) as HF. cbn beta in HF. rewrite Hh in HF.
    unfold has_fact, uw_fact in HF. unfold pm_short. fold sp0z in SPM. rewrite <- SPM.
    destruct (hole_short h); [|destruct (h <? 4)%nat];
      pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ HF) as UR; rewrite uE_var in UR;
      (destruct (Z.leb_spec 96 (16 * vE E 10)); destruct (Z.leb_spec (16 * vE E 10) 160); cbn [andb]; try reflexivity; exfalso; lia).
  Qed.
  Lemma hole_sel_here : forall w, world_ok w (pm_short sp0z) g -> hole_sel w h = true.
  Proof.
    intros [wu wb] [H1 H2]. unfold hole_sel. cbn [w_uw w_brk] in *. rewrite hole_short_pm in H1. rewrite H1, H2. reflexivity.
  Qed.

  Lemma Mr_some : forall a b, MR a = Some b -> FULL a = Some b.
  Proof. intros a b H. unfold Mr, mrestrict in H. destruct (HID a); [discriminate | exact H]. Qed.
  Lemma Mr_vis_none : forall a, MR a = None -> HID a = false -> FULL a = None.
  Proof. intros a H Hv. unfold Mr, mrestrict in H. rewrite Hv in H. exact H. Qed.
  Lemma rdn_Mr_full : forall n a bs, rdn ASEGS MR a n = Some bs ->
    (forall i, 0 <= i < Z.of_nat n -> HID (Z_to_bv 64 (bv_unsigned a + i)) = false) -> rdn ASEGS FULL a n = Some bs.
  Proof.
    induction n as [|n IH]; intros a bs H Hv; [exact H|]. cbn [rdn] in H |- *.
    assert (H0 : HID a = false) by (pose proof (Hv 0 ltac:(lia)) as V; rewrite Z.add_0_r, Z_to_bv_bv_unsigned in V; exact V).
    assert (HM : MR a = FULL a) by (unfold Mr, mrestrict; rewrite H0; reflexivity). rewrite HM in H.
    destruct (match FULL a with Some b => Some b | None => seg_rom ASEGS a end) as [b|]; [|discriminate].
    destruct (rdn ASEGS MR (a + 1)%bv n) as [rest|] eqn:Hr; [|discriminate].
    rewrite (IH _ _ Hr); [exact H|]. intros i Hi.
    replace (Z_to_bv 64 (bv_unsigned (a + 1)%bv + i)) with (Z_to_bv 64 (bv_unsigned a + (1 + i))); [apply Hv; lia|].
    apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. rewrite bv_add_unsigned. unfold bv_wrap.
    change (bv_unsigned (1%bv : word)) with 1. rewrite Zplus_mod_idemp_l. f_equal. lia.
  Qed.

  Ltac prepC :=
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (Hcls & VR06 & REL & VB06 & V0 & VTID & V6 & V10 & SP & SPM & BRK & V1 & V2 & STK & TOPm & PGD & V6' & V10' & VSP);
    let B := fresh "B" in let Bg := fresh "Bg" in let B13 := fresh "B13" in
    pose proof (KB sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as B; cbv zeta in B; destruct B as [B B13];
    unfold pm_kernel_placed in B; rewrite Forall_app in B; destruct B as [B Bg];
    unfold Xof in B, Bg, B13;
    cbn [ps_tid ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted] in B, Bg, B13;
    repeat (apply Forall_cons_iff in B as [? B]); cbn [fst snd] in *;
    pose proof (u64_range brk0) as ?Hb0; pose proof (u64_range sp0) as ?Hs0; unfold sp0z, brk0z in *.

  Lemma csym_den : forall s, let bk := csym_base g cls s in
    uE E (fst bk) + snd bk = csym_val sp0z brk0z X s /\ uE E (fst bk) = lden E (lin_of (fst bk)) /\ 0 <= uE E (fst bk) + snd bk.
  Proof.
    prepC. intros s.
    assert (HP : forall k, 4096 * vE E k < 2 ^ 64 -> uE E (pgE k) = 4096 * vE E k /\ lden E (lin_of (pgE k)) = 4096 * vE E k).
    { intros k Hk. unfold uE, pgE. cbn [edenot lin_of]. rewrite u_mul64, u_lit64a.
      change (bv_unsigned (ev E k)) with (vE E k). pose proof (u64_range (ev E k)) as Rk. change (bv_unsigned (ev E k)) with (vE E k) in Rk.
      replace (4096 mod 2 ^ 64) with 4096 by reflexivity. rewrite Z.mod_small by lia.
      split; [reflexivity|]. unfold lscale, lden. cbn -[Z.mul Z.add uE].
      change (snorm (4096 * 0)) with 0. change (snorm (4096 * 1)) with 4096. cbn [Z.eqb tden]. rewrite uE_var. lia. }
    assert (HU0 : uE E (ELit 0) = 0 /\ lden E (lin_of (ELit 0)) = 0).
    { unfold uE. cbn [edenot]. rewrite u_lit64a. split; reflexivity. }
    assert (HRI : uE E e_ri' = 4096 * vE E K_B06 - 4096 * vE E K_R06 /\ lden E (lin_of e_ri') = 4096 * vE E K_B06 - 4096 * vE E K_R06).
    { split.
      - unfold uE, e_ri'. cbn [edenot]. rewrite u_add64, !u_mul64, !u_lit64a.
        change (bv_unsigned (ev E K_B06)) with (vE E K_B06). change (bv_unsigned (ev E K_R06)) with (vE E K_R06).
        replace (4096 mod 2 ^ 64) with 4096 by reflexivity. replace (-4096 mod 2 ^ 64) with (2^64 - 4096) by reflexivity.
        rewrite (Z.mod_small (4096 * vE E K_B06)) by lia.
        elim_div ((2 ^ 64 - 4096) * vE E K_R06) (2 ^ 64). elim_div (4096 * vE E K_B06 + rm) (2 ^ 64). lia.
      - vm_compute (lin_of e_ri'). unfold lden. cbn [fst snd tden]. rewrite !uE_var. unfold K_B06, K_R06. lia. }
    assert (HSP : uE E e_sp0' = 32768 * vE E 0 + 4096 * vE E 6 + 16 * vE E 10 /\ lden E (lin_of e_sp0') = 32768 * vE E 0 + 4096 * vE E 6 + 16 * vE E 10).
    { split.
      - unfold uE, e_sp0'. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_lit64a.
        change (bv_unsigned (ev E 0)) with (vE E 0). change (bv_unsigned (ev E 6)) with (vE E 6). change (bv_unsigned (ev E 10)) with (vE E 10).
        replace (32768 mod 2 ^ 64) with 32768 by reflexivity. replace (16 mod 2 ^ 64) with 16 by reflexivity. replace (4096 mod 2 ^ 64) with 4096 by reflexivity.
        rewrite !Z.mod_small by lia. reflexivity.
      - vm_compute (lin_of e_sp0'). unfold lden. cbn [fst snd tden]. rewrite !uE_var. lia. }
    assert (HPG : uE E e_pg' = 32768 * vE E 0 + 4096 * vE E 6 /\ lden E (lin_of e_pg') = 32768 * vE E 0 + 4096 * vE E 6).
    { split.
      - unfold uE, e_pg'. cbn [edenot]. rewrite !u_add64, !u_mul64, !u_lit64a.
        change (bv_unsigned (ev E 0)) with (vE E 0). change (bv_unsigned (ev E 6)) with (vE E 6).
        replace (32768 mod 2 ^ 64) with 32768 by reflexivity. replace (4096 mod 2 ^ 64) with 4096 by reflexivity.
        rewrite !Z.mod_small by lia. reflexivity.
      - vm_compute (lin_of e_pg'). unfold lden. cbn [fst snd tden]. rewrite !uE_var. lia. }
    assert (HSTK : pm_stack_top sp0z = 32768 * vE E 0 + 4096 * vE E 6 + stk_up cls).
    { unfold sp0z. rewrite STK. clearbody X KNF. clear -V10 Hcls. destruct (hole_class h) as [|[|]]; cbn [stk_up wlo whi] in *; destruct (Z.leb_spec 11 (vE E 10)); lia. }
    pose proof (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL) as HRIv.
    destruct s; cbn [csym_base csym_val fst snd];
      repeat match goal with |- context [uE E (pgE ?k)] => let Hk := fresh in destruct (HP k ltac:(lia)) as [-> Hk]; rewrite Hk end;
      rewrite ?(proj1 HU0), ?(proj2 HU0), ?(proj1 HRI), ?(proj2 HRI), ?(proj1 HSP), ?(proj2 HSP), ?(proj1 HPG), ?(proj2 HPG), ?HSTK;
      unfold X in *; rewrite ?HRIv; unfold Xof; cbn [ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted];
      unfold sp0z, brk0z in *; try lia.
    -   clearbody X KNF. destruct (hole_granted h); cbn [fst snd].
      + rewrite ?(proj1 HU0), ?(proj2 HU0). lia.
      + apply Forall_inv in Bg. cbn [fst snd] in Bg. destruct (HP K_META ltac:(lia)) as [-> ->]. lia.
    -   clearbody X KNF. assert (0 <= stk_up cls <= 4096) by (clear; destruct (hole_class h) as [|[|]]; cbn; lia). lia.
    -   assert (H512 : uE E (EMd Instr.M_MUL (ELit 512) (EVar K_B16)) = 512 * vE E K_B16).
      { unfold uE. cbn [edenot]. rewrite u_mul64, u_lit64a. change (bv_unsigned (ev E K_B16)) with (vE E K_B16).
        replace (512 mod 2 ^ 64) with 512 by reflexivity. apply Z.mod_small. lia. }
      rewrite H512. pose proof (u64_range (ev E K_B16)) as R16. change (bv_unsigned (ev E K_B16)) with (vE E K_B16) in R16.
      clearbody X KNF.
      repeat match goal with H : _ |- _ => lazymatch type of H with 0 <= vE E K_B16 < _ => fail | env => fail | _ => clear H end end.
      split; [unfold pm_sh; replace (4096 * vE E K_B16) with (512 * vE E K_B16 * 8) by lia; rewrite Z.div_mul by lia; lia|].
      split; [|lia]. unfold lscale, lden. vm_compute (lin_of (EMd Instr.M_MUL (ELit 512) (EVar K_B16))). cbn [fst snd tden]. rewrite uE_var. unfold K_B16. lia.
  Qed.

  Lemma uE_lit : forall n, 0 <= n < 2 ^ 64 -> uE E (ELit n) = n.
  Proof. intros n Hn. unfold uE. cbn [edenot]. rewrite u_lit64a. apply Z.mod_small. exact Hn. Qed.

  Theorem zero_sound : forall w a n, zero_check_w w a n = true -> world_ok w (pm_short sp0z) g -> 0 <= n < 2 ^ 64 ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (cx_val sp0z brk0z X a + i)) = Some (Z_to_bv 8 0).
  Proof.
    intros w [s off] n H Hw Hn i Hi. apply (all_holes_w_here w) in H; [|exact (hole_sel_here w Hw)]. cbn [fst snd] in H.
    destruct (csym_den s) as (D1 & D2 & D3). destruct (csym_base g cls s) as [b k] eqn:CB. cbn [fst snd] in D1, D2, D3.
    rewrite kzero_xB_eqf in H.
    destruct (kzero_x_sound _ _ _ _ _ _ _ _ KNF KNF H) as (Z0 & _ & _).
    specialize (Z0 i). unfold elenZ in Z0. fold (uE E (ELit n)) in Z0. rewrite (uE_lit n Hn) in Z0. specialize (Z0 Hi).
    apply Mr_some. unfold estart in Z0. cbn [a_base a_off] in Z0. fold (uE E b) in Z0.
    unfold cx_val. cbn [fst snd]. rewrite <- D1. replace (uE E b + k + off + i) with (uE E b + (k + off) + i) by lia. exact Z0.
  Qed.

  Theorem fill_sound : forall w a n c, fill_check_w w a n c = true -> world_ok w (pm_short sp0z) g ->
    forall i, 0 <= i < n -> FULL (Z_to_bv 64 (cx_val sp0z brk0z X a + i)) = Some (Z_to_bv 8 c).
  Proof.
    intros w [s off] n c H Hw i Hi. apply (all_holes_w_here w) in H; [|exact (hole_sel_here w Hw)]. cbn [fst snd] in H.
    destruct (csym_den s) as (D1 & D2 & D3). destruct (csym_base g cls s) as [b k] eqn:CB. cbn [fst snd] in D1, D2, D3.
    apply existsb_exists in H as [K [HK HF]]. pose proof (proj1 (Forall_forall _ _) KNF K HK) as KO.
    apply Mr_some. unfold cx_val. cbn [fst snd]. rewrite <- D1.
    assert (GEN : forall zk zn (cv : Z),
      (Z.leb zk (k + off) && Z.leb (k + off + n) (zk + zn) && Z.leb 0 zn && Z.ltb zn (2 ^ 62)) = true ->
      (forall i0, 0 <= i0 < elenZ E (ELit zn) -> MR (Z_to_bv 64 (estart E (SA b zk) + i0)) = Some (Z_to_bv 8 cv)) ->
      MR (Z_to_bv 64 (uE E b + k + off + i)) = Some (Z_to_bv 8 cv)).
    { intros zk zn cv HB KO'. apply andb_prop in HB as [HB H4]. apply andb_prop in HB as [HB H3]. apply andb_prop in HB as [H1 H2].
      apply Z.leb_le in H1. apply Z.leb_le in H2. apply Z.leb_le in H3. apply Z.ltb_lt in H4.
      unfold elenZ in KO'. fold (uE E (ELit zn)) in KO'. rewrite (uE_lit zn ltac:(lia)) in KO'.
      unfold estart in KO'. cbn [a_base a_off] in KO'. fold (uE E b) in KO'.
      replace (uE E b + k + off + i) with (uE E b + zk + (k + off + i - zk)) by lia. apply KO'. lia. }
    destruct K as [| [zb zk] [zn| | | | | | |] | | | | | | | [zb zk] [zn| | | | | | |] zc |]; try discriminate HF; cbn [fill1] in HF.
    - apply andb_prop in HF as [HF H6]. apply andb_prop in HF as [HF H5]. apply andb_prop in HF as [HF H4]. apply andb_prop in HF as [HF H3].
      apply andb_prop in HF as [H1 H2]. apply expr_eqb_eq in H1. subst zb. apply Z.eqb_eq in H2. subst c.
      cbn [kentry_ok] in KO. destruct KO as [_ KO]. apply (GEN zk zn 0); [|exact KO]. rewrite H3, H4, H5, H6. reflexivity.
    - apply andb_prop in HF as [HF H6]. apply andb_prop in HF as [HF H5]. apply andb_prop in HF as [HF H4]. apply andb_prop in HF as [HF H3].
      apply andb_prop in HF as [H1 H2]. apply expr_eqb_eq in H1. subst zb. apply Z.eqb_eq in H2. subst c.
      cbn [kentry_ok] in KO. destruct KO as [_ KO]. apply (GEN zk zn zc); [|exact KO]. rewrite H3, H4, H5, H6. reflexivity.
  Qed.

  Lemma argH0_low : forall z, 0 <= z < sp0z + 8 * Z.of_nat (length (in_argv inp)) + 16 ->
    argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) E (Z_to_bv 64 z) = false.
  Proof.
    intros z Hz. pose proof Vsp as Vsp'. destruct Vsp' as [Vlo [Vhi _]]. unfold sp_window_lo, sp_window_hi in Vlo, Vhi. unfold sp0z in Hz.
    pose proof (len_av APH sp0 rdraw _ (in_envp inp) (in_uid inp) (in_hwcap inp) Vav) as LA.
    unfold argH0. apply andb_false_iff. left. unfold argB0. rewrite u_of_Z by lia.
    apply orb_false_iff. split; apply andb_false_iff; left; apply Z.leb_gt; lia.
  Qed.

  Lemma hid_img : forall z, 65536 <= z < 7241728 -> HID (Z_to_bv 64 z) = false.
  Proof.
    intros z Hz. pose proof Vsp as Vsp'. destruct Vsp' as [Vlo _]. unfold sp_window_lo in Vlo.
    unfold hid. apply orb_false_iff. split; [apply argH0_low; unfold sp0z; lia|].
    apply negb_false_iff. unfold vis. rewrite u_of_Z by lia. replace (in_hull ASAN_H z) with true; [reflexivity|].
    symmetry. unfold in_hull. change (img_lo ASAN_H) with 65536. change (img_hi ASAN_H) with 7241728.
    apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma brk_facts : g = true -> 7241728 <= brk0z /\ brk0z + 12288 <= 2147446784 /\ 4096 * vE E 5 = brk0z.
  Proof.
    intros Hg. destruct (lzc_parts h ch Hh) as (_ & _ & _ & G5 & _). specialize (G5 Hg).
    pose proof (cs_range _ _ _ _ _ _ _ _ _ _ _ _ _ HC _ _ _ G5) as R5. rewrite uE_var in R5.
    pose proof (BRKg sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC Hg) as B5. fold brk0z in B5.
    pose proof (pso_brk _ _ _ _ (pm_syms_ok_open sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) Hg) as [PB _].
    unfold ALOWSH_LO in PB. fold brk0z in PB. lia.
  Qed.
  Lemma VISK_bound : forall z, zinP z (VISK sp0z brk0z X) -> 4096 <= z < page_down sp0z - 8388608.
  Proof.
    intros z. prepC.
    unfold VISK, VISZ0. unfold X. rewrite (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL). unfold Xof.
    cbn [firstn ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted].
    destruct (hole_granted h) eqn:Hg; [destruct (brk_facts Hg) as (BF1 & BF2 & BF3); unfold brk0z in BF1, BF2, BF3 | apply Forall_inv in Bg; cbn [fst snd] in Bg]; cbn [zinP fst snd];
      intros HV; zsolveT.
  Qed.

  Lemma VM_Z : forall z, zinP z (VISK sp0z brk0z X) -> zinP z (PM_MAPS brk0z X).
  Proof.
    intros z. prepC.
    unfold VISK, VISZ0, PM_MAPS, pm_meta_map. unfold X. rewrite (RI_lin (Xof g E) (4096 * vE E K_B06) (vE E K_R06) eq_refl REL). unfold Xof.
    cbn [firstn ps_b04 ps_b05 ps_b06 ps_b08 ps_b09 ps_b10 ps_b11 ps_b12 ps_b13 ps_b16 ps_b19r ps_b20 ps_b21 ps_b22 ps_b23 ps_granted].
    destruct (hole_granted h) eqn:Hg; [destruct (brk_facts Hg) as (BF1 & BF2 & BF3); unfold brk0z in BF1, BF2, BF3 | apply Forall_inv in Bg; cbn [fst snd] in Bg]; cbn [zinP fst snd];
      intros HV; zsolveT.
  Qed.

  Lemma hid_vis : forall z, zinP z (VISK sp0z brk0z X) -> ~ zinP z (PM_NOACC brk0z X) -> HID (Z_to_bv 64 z) = false.
  Proof.
    intros z HV HN. pose proof (VISK_bound z HV) as Hz. unfold sp0z, brk0z, X in *.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & V0 & _ & _ & _ & SP & _ & _ & _ & _ & _ & TOPm & PGD & V6' & V10' & VSP).
    unfold hid. apply orb_false_iff. split; [apply argH0_low; unfold sp0z; lia|].
    apply negb_false_iff. unfold vis. rewrite u_of_Z by lia.
    destruct (in_hull ASAN_H z) eqn:IH; [reflexivity|]. cbn [orb].
    destruct (TOP model <=? z); [reflexivity|]. cbn [orb].
    rewrite (PM_maps_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    rewrite (PM_noacc_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    rewrite (in_ivs_zz sp0 brk0 _ _ (zz_ok_maps sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)).
    rewrite (in_ivs_zz sp0 brk0 _ _ (zz_ok_noacc sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)).
    replace (zin z (PM_MAPS (bv_unsigned brk0) (Xof g E))) with true by (symmetry; apply zin_iff; apply VM_Z; exact HV).
    destruct (zin z (PM_NOACC (bv_unsigned brk0) (Xof g E))) eqn:NA; [exfalso; apply HN; apply zin_iff; exact NA|]. cbn [negb andb].
    apply orb_true_intro. right. unfold in_allow. apply orb_true_intro. left.
    unfold in_vis. apply existsb_exists.
    destruct (VISZ0_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [V1 _].
    apply zinP_In in HV as [p [Hp Hb]]. apply VISK_VISZ0 in Hp. rewrite <- V1 in Hp. apply in_map_iff in Hp as [q [Hq Hin]].
    exists q. split; [exact Hin|]. rewrite <- Hq in Hb. cbn [fst snd] in Hb. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma hid_sh : forall z a n, In (a, n) (VISZ0 sp0z brk0z X) -> 0x7fff8000 + a / 8 <= z < 0x7fff8000 + (a + n) / 8 ->
    zinP z (PM_MAPS brk0z X) -> ~ zinP z (PM_NOACC brk0z X) -> HID (Z_to_bv 64 z) = false.
  Proof.
    intros z a n HIN Hsh HM HN. unfold sp0z, brk0z, X in *.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & V0 & _ & _ & _ & SP & _ & _ & _ & _ & _ & TOPm & PGD & V6' & V10' & VSP).
    assert (Ha : 0 <= a /\ a + n <= 140737488355328).
    { pose proof (proj1 (Forall_forall _ _) (VISZ_facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) _
                    ltac:(unfold VISZ; apply in_app_iff; left; exact HIN)) as VF.
      cbn [fst snd] in VF. destruct VF as [(F1 & F2 & F3 & F4) | [F | F]]; [lia| |]; injection F as F1 F2; lia. }
    assert (Hz : 0 <= z < 17594333495296) by lia.
    unfold hid. apply orb_false_iff. split; [apply argH0_low; unfold sp0z; lia|].
    apply negb_false_iff. unfold vis. rewrite u_of_Z by lia.
    destruct (in_hull ASAN_H z) eqn:IH; [reflexivity|]. cbn [orb].
    destruct (TOP model <=? z); [reflexivity|]. cbn [orb].
    rewrite (PM_maps_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    rewrite (PM_noacc_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC).
    rewrite (in_ivs_zz sp0 brk0 _ _ (zz_ok_maps sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)).
    rewrite (in_ivs_zz sp0 brk0 _ _ (zz_ok_noacc sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC)).
    replace (zin z (PM_MAPS (bv_unsigned brk0) (Xof g E))) with true by (symmetry; apply zin_iff; exact HM).
    destruct (zin z (PM_NOACC (bv_unsigned brk0) (Xof g E))) eqn:NA; [exfalso; apply HN; apply zin_iff; exact NA|]. cbn [negb andb].
    apply orb_true_intro. right. unfold in_allow. apply orb_true_intro. right.
    unfold in_sh. apply existsb_exists.
    destruct (VISZ0_eq sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as [V1 _].
    pose proof HIN as HIN0. rewrite <- V1 in HIN0. apply in_map_iff in HIN0 as [q [Hq Hin]].
    exists q. split; [exact Hin|]. unfold sh_lo, sh_hi. injection Hq as H1 H2. rewrite H1, H2.
    change (shadow_off ASAN_H) with 0x7fff8000. apply andb_true_intro. split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
  Qed.

  Lemma hid_stack : forall z, sp0z - 0x800000 <= z < sp0z + 8 * Z.of_nat (length (in_argv inp)) + 16 -> HID (Z_to_bv 64 z) = false.
  Proof.
    intros z Hz. pose proof Vsp as Vsp'. destruct Vsp' as [Vlo [Vhi _]]. unfold sp_window_lo, sp_window_hi in Vlo, Vhi.
    pose proof (facts sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Hh HC) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & TOPm & _). fold sp0z in TOPm.
    pose proof (len_av APH sp0 rdraw _ (in_envp inp) (in_uid inp) (in_hwcap inp) Vav) as LA. unfold sp0z in Hz, TOPm.
    unfold hid. apply orb_false_iff. split; [apply argH0_low; unfold sp0z; lia|].
    apply negb_false_iff. unfold vis. rewrite u_of_Z by lia.
    replace (TOP model <=? z) with true by (symmetry; apply Z.leb_le; lia). destruct (in_hull ASAN_H z); reflexivity.
  Qed.

  Theorem bytes_sound : forall w a zs, bytes_check_w w a zs = true -> world_ok w (pm_short sp0z) g ->
    0 <= cx_val sp0z brk0z X a -> cx_val sp0z brk0z X a + Z.of_nat (length zs) <= 2 ^ 64 ->
    (forall i, 0 <= i < Z.of_nat (length zs) -> HID (Z_to_bv 64 (cx_val sp0z brk0z X a + i)) = false) ->
    rdn ASEGS FULL (Z_to_bv 64 (cx_val sp0z brk0z X a)) (length zs) = Some (map (Z_to_bv 8) zs).
  Proof.
    intros w [s off] zs H Hw HR1 HR2 Hv. apply (all_holes_w_here w) in H; [|exact (hole_sel_here w Hw)]. cbn [fst snd] in H.
    destruct (csym_den s) as (D1 & D2 & D3). destruct (csym_base g cls s) as [b k] eqn:CB. cbn [fst snd] in D1, D2, D3.
    rewrite !kread_bytesB_eqf' in H.

    assert (EX : exists kk, know_ok ASEGS E MR kk /\ kread_bytes ASEGS (length zs) kk b (k + off) = Some zs).
    { set (kf := List.filter (ksel b (k + off) (k + off + Z.of_nat (length zs))) (kn ch)) in H.
      assert (KNFf : know_ok ASEGS E MR kf).
      { apply Forall_forall. intros K HK. unfold kf in HK. apply filter_In in HK as [HK _]. exact (proj1 (Forall_forall _ _) KNF K HK). }
      assert (LE : forall l, list_eqb Z.eqb l zs = true -> l = zs) by (intros l Hl; apply (list_eqb_eq Z.eqb) in Hl; [exact Hl|intros x y Hxy; apply Z.eqb_eq; exact Hxy]).
      destruct (kread_bytes ASEGS (length zs) kf b (k + off)) as [zs1|] eqn:K1.
      - destruct (list_eqb Z.eqb zs1 zs) eqn:L1.
        + exists kf. split; [exact KNFf|]. pose proof (LE _ L1) as EQ. subst zs1. exact K1.
        + destruct (kread_bytes ASEGS (length zs) (kn ch) b (k + off)) as [zs'|] eqn:KR; [|discriminate]. exists (kn ch). split; [exact KNF|]. pose proof (LE _ H) as EQ. subst zs'. exact KR.
      - destruct (kread_bytes ASEGS (length zs) (kn ch) b (k + off)) as [zs'|] eqn:KR; [|discriminate]. exists (kn ch). split; [exact KNF|]. pose proof (LE _ H) as EQ. subst zs'. exact KR. }
    destruct EX as (kk & KNk & KR).
    unfold cx_val in *. cbn [fst snd] in *. rewrite <- D1 in HR1, HR2, Hv |- *.
    assert (HE : estart E (SA b (k + off)) = uE E b + k + off) by (unfold estart; cbn [a_base a_off]; fold (uE E b); lia).
    destruct (kread_bytes_sound _ _ _ _ _ _ _ _ KNk KR ltac:(rewrite HE; lia) ltac:(rewrite HE; lia)) as (RD & _ & _).
    rewrite HE in RD. apply (rdn_Mr_full _ _ _ RD). intros i Hi. rewrite u_of_Z by lia. apply Hv. exact Hi.
  Qed.

  Theorem word_sound : forall w a v, word_check_w w a v = true -> world_ok w (pm_short sp0z) g ->
    0 <= cx_val sp0z brk0z X a -> cx_val sp0z brk0z X a + 8 <= 2 ^ 64 ->
    (forall i, 0 <= i < 8 -> HID (Z_to_bv 64 (cx_val sp0z brk0z X a + i)) = false) ->
    rdn ASEGS FULL (Z_to_bv 64 (cx_val sp0z brk0z X a)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (cx_val sp0z brk0z X v))).
  Proof.
    intros w [s off] [vs voff] H Hw HR1 HR2 Hv. apply (all_holes_w_here w) in H; [|exact (hole_sel_here w Hw)]. cbn [fst snd] in H.
    destruct (csym_den s) as (D1 & D2 & D3). destruct (csym_base g cls s) as [b k] eqn:CB. cbn [fst snd] in D1, D2, D3.
    destruct (csym_den vs) as (W1 & W2 & W3). unfold cx_vexpr in H. cbn [fst snd] in H. destruct (csym_base g cls vs) as [vb vk] eqn:CV. cbn [fst snd] in W1, W2, W3.
    rewrite kread8eB_eqf in H.
    destruct (kread8e ASEGS (kn ch) b (k + off)) as [e|] eqn:KR; [|discriminate].
    apply lin_eqz_eq in H.
    unfold cx_val in *. cbn [fst snd] in *. rewrite <- D1 in HR1, HR2, Hv |- *. rewrite <- W1.
    assert (HE : estart E (SA b (k + off)) = uE E b + k + off) by (unfold estart; cbn [a_base a_off]; fold (uE E b); lia).
    assert (FL : flat E (SA b (k + off)) 8) by (unfold flat; rewrite HE; lia).
    destruct (kread8e_piece _ _ _ _ _ _ _ KNF KR FL) as (bs & RD & Hlen & Hbs).
    rewrite HE in RD. rewrite (rdn_Mr_full _ _ _ RD) by (intros i Hi; rewrite u_of_Z by lia; apply Hv; exact Hi).
    f_equal. rewrite <- Hbs. f_equal.
    rewrite <- (Z_to_bv_bv_unsigned 64 (edenot E e)). apply eqm_Z_to_bv.
    eapply eqm_trans; [apply eqm_sym; apply lin_of_sound|]. rewrite H.
    eapply eqm_trans; [apply lin_of_sound|]. unfold uE at 1.
    change (edenot E (EAlu Instr.ALU_ADD vb (ELit (vk + voff)))) with (Sem.alu64 Instr.ALU_ADD (edenot E vb) (edenot E (ELit (vk + voff)))).
    eapply eqm_trans; [apply u_add_eqm|]. fold (uE E vb). rewrite edenot_lit. replace (uE E vb + vk + voff) with (uE E vb + (vk + voff)) by lia.
    apply eqm_add; [apply eqm_refl | apply eqm_u_lit].
  Qed.

  Theorem img_sound : forall lo hi, img_check lo hi = true -> forall a, lo <= a < hi -> FULL (Z_to_bv 64 a) = None.
  Proof.
    intros lo hi H a Ha. unfold img_check in H. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2].
    apply Z.leb_le in H1. apply Z.leb_le in H2. apply all_holes_here in H3.
    apply existsb_exists in H3 as [K [HK HI]]. destruct K; try discriminate HI. cbn [img1] in HI.
    apply andb_prop in HI as [HI1 HI2]. apply Z.leb_le in HI1. apply Z.leb_le in HI2.
    pose proof (proj1 (Forall_forall _ _) KNF _ HK) as KO. cbn [kentry_ok] in KO. destruct KO as (_ & _ & KO).
    apply Mr_vis_none; [apply KO; lia | apply hid_img; lia].
  Qed.

  Definition visibleZ (sp0z brk0z argc : Z) (X : pm_syms) (z : Z) : Prop :=
    (65536 <= z < 7241728)
    \/ (zinP z (VISK sp0z brk0z X) /\ ~ zinP z (PM_NOACC brk0z X))
    \/ (sp0z - 0x800000 <= z < sp0z + 8 * argc + 16)
    \/ ((exists a n, In (a, n) (VISZ0 sp0z brk0z X) /\ 0x7fff8000 + a / 8 <= z < 0x7fff8000 + (a + n) / 8)
        /\ zinP z (PM_MAPS brk0z X) /\ ~ zinP z (PM_NOACC brk0z X)).
  Lemma visibleZ_hid : forall z, visibleZ sp0z brk0z (Z.of_nat (length (in_argv inp))) X z -> HID (Z_to_bv 64 z) = false.
  Proof.
    intros z [Hz|[(H1 & H2)|[Hz|((a & n & HIN & Hsh) & HM & HN)]]];
      [apply hid_img; exact Hz | apply hid_vis; assumption | apply hid_stack; exact Hz | eapply hid_sh; eassumption].
  Qed.

  Lemma args_block : forall a, argB0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) a = true ->
    FULL a = wrap_mem APH sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a.
  Proof.
    intros a Ha. pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as SI. apply (proj2 SI).
    rewrite (argH0_SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) Vsp Vav Vev Vfit E FULL a SI). exact Ha.
  Qed.
End CELLS.

Record PMC (sp0 : word) (rdraw : EntryDraw) (inp : ProcInput) (brk0z : Z) (X : pm_syms) (m : word -> option byte) : Prop := MkPMC {
  pmc_zero_w  : forall w a n, zero_check_w w a n = true -> world_ok w (pm_short (bv_unsigned sp0)) (ps_granted X) -> 0 <= n < 2 ^ 64 ->
                forall i, 0 <= i < n -> m (Z_to_bv 64 (cx_val (bv_unsigned sp0) brk0z X a + i)) = Some (Z_to_bv 8 0);
  pmc_fill_w  : forall w a n c, fill_check_w w a n c = true -> world_ok w (pm_short (bv_unsigned sp0)) (ps_granted X) ->
                forall i, 0 <= i < n -> m (Z_to_bv 64 (cx_val (bv_unsigned sp0) brk0z X a + i)) = Some (Z_to_bv 8 c);
  pmc_bytes_w : forall w a zs, bytes_check_w w a zs = true -> world_ok w (pm_short (bv_unsigned sp0)) (ps_granted X) ->
                0 <= cx_val (bv_unsigned sp0) brk0z X a -> cx_val (bv_unsigned sp0) brk0z X a + Z.of_nat (length zs) <= 2 ^ 64 ->
                (forall i, 0 <= i < Z.of_nat (length zs) -> visibleZ (bv_unsigned sp0) brk0z (Z.of_nat (length (in_argv inp))) X (cx_val (bv_unsigned sp0) brk0z X a + i)) ->
                rdn ASEGS m (Z_to_bv 64 (cx_val (bv_unsigned sp0) brk0z X a)) (length zs) = Some (map (Z_to_bv 8) zs);
  pmc_word_w  : forall w a v, word_check_w w a v = true -> world_ok w (pm_short (bv_unsigned sp0)) (ps_granted X) ->
                0 <= cx_val (bv_unsigned sp0) brk0z X a -> cx_val (bv_unsigned sp0) brk0z X a + 8 <= 2 ^ 64 ->
                (forall i, 0 <= i < 8 -> visibleZ (bv_unsigned sp0) brk0z (Z.of_nat (length (in_argv inp))) X (cx_val (bv_unsigned sp0) brk0z X a + i)) ->
                rdn ASEGS m (Z_to_bv 64 (cx_val (bv_unsigned sp0) brk0z X a)) 8
                = Some (word_to_le_bytes 8 (Z_to_bv 64 (cx_val (bv_unsigned sp0) brk0z X v)));
  pmc_img   : forall lo hi, img_check lo hi = true -> forall a, lo <= a < hi -> m (Z_to_bv 64 a) = None;
  pmc_args  : forall a, argB0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) a = true ->
                m a = wrap_mem APH sp0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp) rdraw a
}.

Lemma world_ok_all : forall s g, world_ok w_all s g.
Proof. intros s g. split; reflexivity. Qed.
Section PMCv2.
  Context (sp0 : word) (rdraw : EntryDraw) (inp : ProcInput) (brk0z : Z) (X : pm_syms) (m : word -> option byte) (MC : PMC sp0 rdraw inp brk0z X m).
  Definition pmc_zero a n (H : zero_check a n = true) := pmc_zero_w _ _ _ _ _ _ MC w_all a n H (world_ok_all _ _).
  Definition pmc_fill a n c (H : fill_check a n c = true) := pmc_fill_w _ _ _ _ _ _ MC w_all a n c H (world_ok_all _ _).
  Definition pmc_bytes a zs (H : bytes_check a zs = true) := pmc_bytes_w _ _ _ _ _ _ MC w_all a zs H (world_ok_all _ _).
  Definition pmc_word a v (H : word_check a v = true) := pmc_word_w _ _ _ _ _ _ MC w_all a v H (world_ok_all _ _).
End PMCv2.

Ltac pmc_simpl := unfold cx_val, csym_val, visibleZ; cbn [fst snd length Z.of_nat Pos.of_succ_nat Pos.succ].

Lemma PMC_open : forall (sp0 brk0 : word) (rdraw : EntryDraw) (inp : ProcInput) (h : nat) (ch : acs) (E : env) (R : bvmap 5 word)
    (FULL : word -> option byte) (model : Model),
  valid_sp sp0 -> valid_brk ASEGS brk0 -> valid_argv (in_argv inp) -> valid_envp (in_envp inp) -> entry_stack_fits sp0 (in_argv inp) (in_envp inp) ->
  HSF_asan h = Some ch ->
  cs_ok ASEGS ASAN_H BothInit.LIMIT (SINV0 APH sp0 rdraw brk0 (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp))
        (argH0 APH sp0 rdraw (in_argv inp) (in_envp inp) (in_uid inp) (in_hwcap inp)) (in_fs inp) E ch R FULL model ->
  PMC sp0 rdraw inp (bv_unsigned brk0) (Xof (hole_granted h) E) FULL.
Proof.
  intros sp0 brk0 rdraw inp h ch E R FULL model Vsp Vbrk Vav Vev Vfit Hh HC. constructor.
  - intros w a n Hc0 Hw Hn. eapply zero_sound; eassumption.
  - intros w a n cc Hc0 Hw. eapply fill_sound; eassumption.
  - intros w a zs Hc0 Hw H1 H2 Hv. eapply bytes_sound; try eassumption.
    intros i Hi. eapply visibleZ_hid; try eassumption. apply Hv. exact Hi.
  - intros w a v Hc0 Hw H1 H2 Hv. eapply word_sound; try eassumption.
    intros i Hi. eapply visibleZ_hid; try eassumption. apply Hv. exact Hi.
  - intros lo hi Hc0. eapply img_sound; eassumption.
  - intros a Ha. eapply args_block; eassumption.
Qed.

Section ALL.
  Variables (sp0 brk0 mbase : word) (rdraw : EntryDraw) (inp : ProcInput) (c : config).
  Hypothesis P : P_main sp0 brk0 mbase rdraw inp c.

End ALL.
