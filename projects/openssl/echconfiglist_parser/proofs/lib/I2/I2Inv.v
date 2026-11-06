(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Uint63 PrimString.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib Require Import HeapCeil.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Lib Require Import PropExec MState Mem Cells Step Frame Exec TacX.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Spec Require Import Prog.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.Ref Require Import RSegs RMalloc_iface_stmt HeapSR_iface ECH_SR.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import FxSteps FxAcc.
From OSSVerify.Proofs.openssl.echconfiglist_parser.lib.I2 Require Import
  W64 ITrie FxSpec FxInstr FxState FxMem FxExec FxRel FxKind FxMemSound FxValSound FxStepSound FxStepMain
  FxRun FxRn FxImage FxHandoff FxCellFrame FxRoFrame FxGeom I2Canon I2Mach I2Image I2Run.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac slia := Zify.zify; xlia zchecker.

(* [comment removed for export] *)
Record gblk : Type := GB { g_tag : int; g_id : bptr; g_addr : Z; g_size : int }.

(* [comment removed for export] *)
Record i2env : Type := I2E {
  q_sp0 : Z;                  (* [comment removed for export] *)
  q_lo : Z;                   (* [comment removed for export] *)
  q_B : Z;                    (* [comment removed for export] *)
  q_mo0 : Model;              (* [comment removed for export] *)
  q_F : bvmap 5 word; q_fc : bv 32;   (* [comment removed for export] *)
  q_m0 : word -> option byte; (* [comment removed for export] *)
  q_LB0 : list block;         (* [comment removed for export] *)
  q_n0 : int;                 (* [comment removed for export] *)
  q_rho0 : int -> word;
  q_G0 : list gblk }.         (* [comment removed for export] *)

Section Inv.
  Context {HCEIL : HeapCeil}.
  Variable H : hsr.
  Variable IMX : fimage.            (* [comment removed for export] *)
  Variable K : i2consts.
  Let IM := im_ro IMX.
  Let RO := ro_of K.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition rb_addr (a : Z) : Prop := exists b, In b (c_rb K) /\ to_Z b = a.
  Definition xw_addr (a : Z) : Prop := (exists c, In c (c_xw K) /\ to_Z c <= a < to_Z c + 8) /\ ~ rb_addr a.
  Definition err_addr (a : Z) : Prop := to_Z (c_errcell K) <= a < to_Z (c_errcell K) + 8 /\ ~ rb_addr a.
  Definition errA : Z := to_Z (c_errcell K) + to_Z (c_errbi K).
  Definition named_addr (Q : i2env) (a : Z) : Prop :=
    exists g, In g (q_G0 Q) /\ g_addr g <= a < g_addr g + to_Z (g_size g).
  Definition client0 (Q : i2env) (a : Z) : Prop := rclient_addr (q_LB0 Q) (q_sp0 Q) a.

  (* [comment removed for export] *)
  Definition xw_cell_ok (c : int) : bool :=
    ((c land 7 =? 0)%uint63)
    && (0x27e000 <=? to_Z c)%Z && (to_Z c + 8 <=? 0x311000)%Z
    && ((to_Z c + 8 <=? RLIBC)%Z || (RCTX + 936 <=? to_Z c)%Z)
    && ((to_Z c + 8 <=? RSSP_GUARD)%Z || (RSSP_GUARD + 8 <=? to_Z c)%Z)
    && ((to_Z c + 8 <=? RGOT_SSP)%Z || (RGOT_SSP + 8 <=? to_Z c)%Z)
    && ((to_Z c + 8 <=? RVMLOCK)%Z || (RVMLOCK + 8 <=? to_Z c)%Z)
    && ((to_Z c + 8 <=? RERRNO)%Z || (RERRNO + 4 <=? to_Z c)%Z).
  Definition K_err_ok : bool :=
    (to_Z (c_errcell K) + to_Z (c_errbi K) =? RERRNO)%Z && ((c_errcell K land 7 =? 0)%uint63) && (to_Z (c_errbi K) + 4 <=? 8)%Z
    && (to_Z (c_tp K) =? RATP)%Z
    && (RREALLOC_STACK <=? to_Z (c_mstack K))%Z && (to_Z (c_mstack K) <=? to_Z (c_stack K))%Z
    && ((c_stack K land 15 =? 0)%uint63) && (to_Z (c_stack K) <=? 2 ^ 40)%Z.
  Definition K_pcs_ok : bool :=
    (c_malloc K =? of_Z RMALLOC_SYM)%uint63 && (c_free K =? of_Z RFREE_SYM)%uint63
    && ((c_realloc K =? of_Z RREALLOC_SYM)%uint63 || (c_realloc K =? 0)%uint63)
    && ((c_aalloc K =? of_Z RAALLOC_SYM)%uint63 || (c_aalloc K =? 0)%uint63).
  Definition K_ro_ok : bool :=
    forallb (fun ac : int * cell => ((fst ac land 7 =? 0)%uint63) && (0x10000 <=? to_Z (fst ac))%Z && (to_Z (fst ac) + 8 <=? 0x311000)%Z
                                    && negb (existsb (fun c => (c =? fst ac)%uint63) (c_xw K))
                                    && negb ((fst ac =? c_errcell K)%uint63)) (c_ro K).
  Definition K_caps_ok : bool :=
    (to_Z (c_cost K) <? 2 ^ 60)%Z && (to_Z (c_cnt K) <? 2 ^ 60)%Z && (to_Z (c_big K) <? 2 ^ 60)%Z.
  Definition K_rb_ok : bool :=
    forallb (fun b : int => (0x10000 <=? to_Z b)%Z && (to_Z b <? 0x311000)%Z) (c_rb K).
  Definition K_ok : bool :=
    forallb xw_cell_ok (c_xw K) && K_err_ok && K_pcs_ok && K_ro_ok && K_caps_ok && K_rb_ok.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Record I2RX (Q : i2env) (st : i2st) (rho : int -> word) (ms : machine_state) (mo : Model)
         (s : PState) (LB : list block) (G : list gblk) : Prop := mkI2RX {
    r_Rn : Rn rsegs IM (i_n st) rho (i_F st) ms ;
    r_canon : canonR (ms_regs ms) ;
    r_fregs : ms_fregs ms = q_F Q ;
    r_fcsr : ms_fcsr ms = q_fc Q ;
    r_rom : ms_rom ms = seg_rom rsegs ;
    r_rho0 : rho 0%uint63 = Z_to_bv 64 0 ;
    r_rho1 : rho 1%uint63 = wa (q_sp0 Q - to_Z (c_stack K)) ;
    r_agree : agree (q_n0 Q) (q_rho0 Q) rho ;
    r_n0 : 2 <= to_Z (q_n0 Q) <= to_Z (i_n st) /\ to_Z (i_n st) < 2 ^ 60 ;
    r_heap : hs_RHEAP H s LB (ms_mem ms) ;
    r_krel : hs_KREL H s mo ;
    r_mpres : hs_MPRES H (q_mo0 Q) mo ;
    r_G : i_blk st = map (fun g => (g_tag g, g_size g)) G ;
    r_Gin : Forall (fun g => In (g_id g, g_addr g, to_Z (g_size g)) LB
                            /\ rho (g_tag g) = wa (g_addr g)
                            /\ 1 <= to_Z (g_size g)
                            /\ 2 <= to_Z (g_tag g) < to_Z (i_n st)
                            /\ exists rg, iget (g_tag g) (f_mem (i_F st)) = Some rg
                                 /\ rg_lo rg = 0%uint63 /\ rg_len rg = g_size g) G ;
    r_Gnodup : List.NoDup (map g_id G) ;
    r_Gtnd : List.NoDup (map g_tag G) ;
    r_Gnew : Forall (fun g => In g (q_G0 Q)
                             \/ ((forall a, client0 Q a -> ~ named_addr Q a ->
                                    ~ (g_addr g <= a < g_addr g + to_Z (g_size g)))
                                 /\ (forall b, In b (q_LB0 Q) -> ~ In (blk_id b) (map g_id (q_G0 Q)) -> g_id g <> blk_id b))) G ;
    r_Gstk : Forall (fun g => stk rsegs (ms_mem ms) (g_addr g) (g_addr g + to_Z (g_size g))) G ;
    r_dom : forall t rg, iget t (f_mem (i_F st)) = Some rg -> t = 0%uint63 \/ t = 1%uint63 \/ In t (map g_tag G) ;
    r_r0 : exists rg0, iget 0%uint63 (f_mem (i_F st)) = Some rg0
             /\ to_Z (rg_lo rg0) = 0x10000 /\ to_Z (rg_len rg0) = 0x311000 /\ rg_dflt rg0 = None
             /\ forall pn p, iget pn (rg_pages rg0) = Some p -> seg_wr_page IMX pn = true /\ pg_kind p = PKUnk ;
    r_r1 : exists rg1, iget 1%uint63 (f_mem (i_F st)) = Some rg1
             /\ rg_lo rg1 = 0%uint63 /\ rg_len rg1 = c_stack K /\ rg_dflt rg1 = Some PKUnk ;
    r_ro : ro_in_r0 RO (f_mem (i_F st)) ;
    r_inb : cells_inb (f_mem (i_F st)) ;
    r_kinds : kinds_unk (f_mem (i_F st)) ;
    r_cost : lb_bytes LB + (to_Z (c_cost K) - to_Z (i_cost st)) <= hs_LIVE_MAX H /\ to_Z (i_cost st) <= to_Z (c_cost K)
             /\ lb_bytes LB <= lb_bytes (q_LB0 Q) + to_Z (i_cost st) ;
    r_cnt : Z.of_nat (length LB) + (to_Z (c_cnt K) - to_Z (i_cnt st)) <= hs_LIVE_CNT_MAX H /\ to_Z (i_cnt st) <= to_Z (c_cnt K)
             /\ Z.of_nat (length LB) <= Z.of_nat (length (q_LB0 Q)) + to_Z (i_cnt st) ;
    r_big : lb_big LB + (to_Z (c_big K) - to_Z (i_big st)) <= hs_LIVE_BIG_MAX H /\ to_Z (i_big st) <= to_Z (c_big K)
             /\ lb_big LB <= lb_big (q_LB0 Q) + to_Z (i_big st) ;
    r_stk : stk rsegs (ms_mem ms) (q_lo Q) (q_sp0 Q) ;
    r_lo : hceil <= q_lo Q /\ q_lo Q <= q_sp0 Q - to_Z (c_stack K) /\ q_sp0 Q <= q_B Q /\ q_sp0 Q mod 16 = 0 /\ q_B Q < 2 ^ 64 ;
    r_auxv : hs_rauxv_ok H (ms_mem ms) (q_B Q) ;
    r_inv : mem_inv rsegs (ms_mem ms) ;
    r_err : stk rsegs (ms_mem ms) errA (errA + 4) ;
    r_LB0 : forall b, In b (q_LB0 Q) -> ~ In (blk_id b) (map g_id (q_G0 Q)) -> In b LB ;
    r_LB0h : forall b, In b (q_LB0 Q) -> 0 <= blk_addr b /\ blk_addr b + blk_size b <= hceil ;
    r_named0 : Forall (fun g => In (g_id g, g_addr g, to_Z (g_size g)) (q_LB0 Q)) (q_G0 Q) /\ List.NoDup (map blk_id (q_LB0 Q)) ;
    r_LBsub : forall b, In b LB -> In b (q_LB0 Q) \/ exists g, In g G /\ b = (g_id g, g_addr g, to_Z (g_size g)) ;
    r_frame : forall a, 0 <= a < 2 ^ 64 -> client0 Q a -> ~ named_addr Q a -> ~ xw_addr a -> ~ err_addr a ->
              ms_mem ms (wa a) = q_m0 Q (wa a)
  }.

  Definition I2R (Q : i2env) (st : i2st) (rho : int -> word) (ms : machine_state) (mo : Model) : Prop :=
    exists s LB G, I2RX Q st rho ms mo s LB G.

  (* [comment removed for export] *)
  Definition cells0_in (M : itrie region) : Prop :=
    forall rg0 pn p ci c, iget 0%uint63 M = Some rg0 -> iget pn (rg_pages rg0) = Some p -> iget ci (pg_cells p) = Some c ->
      let a := to_Z pn * 4096 + to_Z ci * 8 in
      (exists x, In x (c_xw K) /\ to_Z x = a) \/ a = to_Z (c_errcell K) \/ (exists cc, In (of_Z a, cc) (c_ro K)).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variable code : itrie finstr.
  Hypothesis Hcode : code_ok rsegs code.
  Hypothesis HK : K_ok = true.
  Hypothesis HHx : heap_sr_hyps_x H.
  Hypothesis Hnw : im_nowr IM.

  Lemma HH : heap_sr_hyps H. Proof. exact (proj1 HHx). Qed.

  (* [comment removed for export] *)
  Definition segW (Q : i2env) (G : list gblk) : list ivl :=
    map (fun c : int => (to_Z c, to_Z c + 8)) (c_xw K)
    ++ [(to_Z (c_errcell K), to_Z (c_errcell K) + 8)]
    ++ [(q_sp0 Q - to_Z (c_stack K), q_sp0 Q)]
    ++ map (fun g => (g_addr g, g_addr g + to_Z (g_size g))) G.

  Lemma outside_app : forall W1 W2 x, outside (W1 ++ W2) x <-> outside W1 x /\ outside W2 x.
  Proof. induction W1 as [|[lo hi] W1 IH]; intros W2 x; cbn; [tauto|]. rewrite IH. tauto. Qed.

  Lemma outside_map : forall {A} (f : A -> ivl) (l : list A) x,
    outside (map f l) x <-> forall y, In y l -> ~ (fst (f y) <= x < snd (f y)).
  Proof.
    induction l as [|y l IH]; intros x; cbn.
    - split; [intros _ y [] | intros _; exact I].
    - destruct (f y) as [lo hi] eqn:Ef. rewrite IH. split.
      + intros [H1 H2] z [<-|Hz]; [rewrite Ef; cbn; exact H1 | exact (H2 z Hz)].
      + intros Hz. split; [specialize (Hz y (or_introl eq_refl)); rewrite Ef in Hz; exact Hz|].
        intros z Hz'. apply Hz. right. exact Hz'.
  Qed.

  Lemma Forall_app_iff : forall {A} (P : A -> Prop) l1 l2, Forall P (l1 ++ l2) <-> Forall P l1 /\ Forall P l2.
  Proof. intros. apply Forall_app. Qed.

  (* [comment removed for export] *)
  Lemma HK_parts : forallb xw_cell_ok (c_xw K) = true /\ K_err_ok = true /\ K_pcs_ok = true /\ K_ro_ok = true /\ K_caps_ok = true.
  Proof. unfold K_ok in HK. rewrite !andb_true_iff in HK. tauto. Qed.
  Lemma HK_rb : forall b, In b (c_rb K) -> 0x10000 <= to_Z b < 0x311000.
  Proof.
    intros b Hb. unfold K_ok in HK. rewrite !andb_true_iff in HK. destruct HK as [_ Hr]. unfold K_rb_ok in Hr.
    rewrite forallb_forall in Hr. specialize (Hr b Hb). apply andb_true_iff in Hr as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. split; assumption.
  Qed.

  Lemma HK_xw : forall c, In c (c_xw K) -> xw_cell_ok c = true.
  Proof. intros c Hc. destruct HK_parts as (Hx & _). rewrite forallb_forall in Hx. exact (Hx c Hc). Qed.

  Lemma HK_caps : to_Z (c_cost K) < 2 ^ 60 /\ to_Z (c_cnt K) < 2 ^ 60 /\ to_Z (c_big K) < 2 ^ 60.
  Proof.
    destruct HK_parts as (_ & _ & _ & _ & Hc). unfold K_caps_ok in Hc. rewrite !andb_true_iff in Hc.
    destruct Hc as [[H1 H2] H3]. apply Z.ltb_lt in H1. apply Z.ltb_lt in H2. apply Z.ltb_lt in H3. repeat split; assumption.
  Qed.

  Lemma HK_pcs : c_malloc K = of_Z RMALLOC_SYM /\ c_free K = of_Z RFREE_SYM
                 /\ (c_realloc K = of_Z RREALLOC_SYM \/ c_realloc K = 0%uint63)
                 /\ (c_aalloc K = of_Z RAALLOC_SYM \/ c_aalloc K = 0%uint63).
  Proof.
    destruct HK_parts as (_ & _ & Hp & _ & _). unfold K_pcs_ok in Hp. rewrite !andb_true_iff, !orb_true_iff in Hp.
    destruct Hp as [[[H1 H2] H3] H4]. apply Uint63.eqb_spec in H1. apply Uint63.eqb_spec in H2.
    repeat split; try assumption.
    - destruct H3 as [H3|H3]; apply Uint63.eqb_spec in H3; [left | right]; exact H3.
    - destruct H4 as [H4|H4]; apply Uint63.eqb_spec in H4; [left | right]; exact H4.
  Qed.

  Lemma xw_cell_ok_spec : forall c, xw_cell_ok c = true ->
    to_Z c mod 8 = 0 /\ 0x27e000 <= to_Z c /\ to_Z c + 8 <= 0x311000
    /\ (to_Z c + 8 <= RLIBC \/ RCTX + 936 <= to_Z c)
    /\ (to_Z c + 8 <= RSSP_GUARD \/ RSSP_GUARD + 8 <= to_Z c)
    /\ (to_Z c + 8 <= RGOT_SSP \/ RGOT_SSP + 8 <= to_Z c)
    /\ (to_Z c + 8 <= RVMLOCK \/ RVMLOCK + 8 <= to_Z c)
    /\ (to_Z c + 8 <= RERRNO \/ RERRNO + 4 <= to_Z c).
  Proof.
    intros c Hc. unfold xw_cell_ok in Hc. rewrite !andb_true_iff, !orb_true_iff in Hc.
    destruct Hc as [[[[[[[H8 Ha] Hb] Hl] Hs] Hg] Hv] He].
    apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8. change (to_Z 0) with 0 in H8.
    rewrite !Z.leb_le in *.
    repeat match goal with H : (_ <=? _)%Z = true \/ (_ <=? _)%Z = true |- _ => rewrite !Z.leb_le in H end.
    repeat split; assumption.
  Qed.

  Lemma HK_err : to_Z (c_errcell K) + to_Z (c_errbi K) = RERRNO /\ to_Z (c_errcell K) mod 8 = 0 /\ to_Z (c_errbi K) + 4 <= 8
                 /\ to_Z (c_tp K) = RATP /\ RREALLOC_STACK <= to_Z (c_mstack K) /\ to_Z (c_mstack K) <= to_Z (c_stack K)
                 /\ to_Z (c_stack K) mod 16 = 0 /\ to_Z (c_stack K) <= 2 ^ 40.
  Proof.
    destruct HK_parts as (_ & HE & _ & _ & _). unfold K_err_ok in HE. rewrite !andb_true_iff in HE.
    destruct HE as [[[[[[[He H8] Hbi] Htp] Hm1] Hm2] H16] H40].
    apply Z.eqb_eq in He. apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8.
    apply Z.leb_le in Hbi. apply Z.eqb_eq in Htp. apply Z.leb_le in Hm1. apply Z.leb_le in Hm2.
    apply Uint63.eqb_spec in H16. apply (f_equal to_Z) in H16.
    rewrite (i63_land_ones (c_stack K) 15%uint63 4 eq_refl ltac:(slia)) in H16. change (2 ^ 4) with 16 in H16.
    apply Z.leb_le in H40.
    repeat split; try assumption; try reflexivity.
  Qed.

  Ltac hk_xw c Hc :=
    let X := fresh "Xw" in
    pose proof (xw_cell_ok_spec c (HK_xw c Hc)) as X;
    destruct X as (? & ? & ? & ? & ? & ? & ? & ?); pose proof (i63_range c).

  Ltac hk_err :=
    let E1 := fresh "Eerr" in let E2 := fresh "Eerr8" in let E3 := fresh "Ebi" in let E4 := fresh "Etp" in
    let E5 := fresh "Em1" in let E6 := fresh "Em2" in let E7 := fresh "Est16" in let E8 := fresh "Est40" in
    destruct HK_err as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8);
    pose proof (i63_range (c_errbi K)); pose proof (i63_range (c_errcell K)); pose proof (i63_range (c_stack K));
    pose proof (i63_range (c_mstack K)).

  Lemma HK_ro : forall a c, In (a, c) (c_ro K) ->
    to_Z a mod 8 = 0 /\ 0x10000 <= to_Z a /\ to_Z a + 8 <= 0x311000 /\ ~ (exists x, In x (c_xw K) /\ x = a) /\ a <> c_errcell K.
  Proof.
    intros a c Hin. destruct HK_parts as (_ & _ & _ & Hro & _). unfold K_ro_ok in Hro.
    rewrite forallb_forall in Hro. specialize (Hro (a, c) Hin). cbn [fst] in Hro. rewrite !andb_true_iff in Hro.
    destruct Hro as [[[[H8 Hlo] Hhi] Hx] He].
    apply Uint63.eqb_spec in H8. apply (f_equal to_Z) in H8. rewrite to_Z_land7 in H8.
    apply Z.leb_le in Hlo. apply Z.leb_le in Hhi. apply negb_true_iff in Hx. apply negb_true_iff in He.
    repeat split; try assumption.
    - intros (x & Hx' & ->). assert (existsb (fun c0 : int => (c0 =? a)%uint63) (c_xw K) = true); [|congruence].
      apply existsb_exists. exists a. split; [exact Hx' | apply Uint63.eqb_refl].
    - intros ->. rewrite Uint63.eqb_refl in He. discriminate.
  Qed.

  (* [comment removed for export] *)
  Lemma fold_iset_in : forall (l : list int) k, In k l -> iget k (fold_right (fun b acc => iset b tt acc) iempty l) = Some tt.
  Proof.
    induction l as [|b l IH]; intros k Hk; [destruct Hk|]. cbn [fold_right]. rewrite iget_iset.
    destruct (k =? b)%uint63 eqn:E; [reflexivity|]. destruct Hk as [->|Hk]; [rewrite Uint63.eqb_refl in E; discriminate | exact (IH k Hk)].
  Qed.
  Lemma fold_iset_inv : forall (l : list int) k u, iget k (fold_right (fun b acc => iset b tt acc) iempty l) = Some u -> In k l.
  Proof.
    induction l as [|b l IH]; intros k u Hg; cbn [fold_right] in Hg; [rewrite iget_iempty in Hg; discriminate|].
    rewrite iget_iset in Hg. destruct (k =? b)%uint63 eqn:E; [apply Uint63.eqb_spec in E; left; symmetry; exact E | right; exact (IH k u Hg)].
  Qed.

  Lemma int_add_small : forall (c j : int), to_Z j < 8 -> to_Z c + 8 <= 2 ^ 62 -> to_Z (c + j)%uint63 = to_Z c + to_Z j.
  Proof.
    intros c j Hj Hc. pose proof (i63_range c). pose proof (i63_range j). rewrite Uint63.add_spec. change wB with (2 ^ 63).
    apply Z.mod_small. slia.
  Qed.

  Lemma in_j8 : forall j : int, In j [0; 1; 2; 3; 4; 5; 6; 7]%uint63 -> 0 <= to_Z j < 8.
  Proof. intros j Hj. cbn [In] in Hj. repeat (destruct Hj as [<-|Hj]; [cbn; slia|]). destruct Hj. Qed.

  Lemma j8_in : forall j : Z, 0 <= j < 8 -> In (of_Z j) [0; 1; 2; 3; 4; 5; 6; 7]%uint63.
  Proof.
    intros j Hj. assert (Hc : j = 0 \/ j = 1 \/ j = 2 \/ j = 3 \/ j = 4 \/ j = 5 \/ j = 6 \/ j = 7) by slia.
    cbn [In]. destruct Hc as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; tauto.
  Qed.

  (* [comment removed for export] *)
  Lemma ro_of_cell : forall a c (j : Z), In (a, c) (c_ro K) -> 0 <= j < 8 ->
    exists k, iget k RO = Some tt /\ to_Z k = to_Z a + j.
  Proof.
    intros a c j Hin Hj. pose proof (HK_ro a c Hin) as (_ & Hlo & Hhi & _).
    exists (a + of_Z j)%uint63. split.
    - unfold RO, ro_of. apply fold_iset_in. unfold ro_bytes. apply in_or_app. left.
      apply in_flat_map. exists (a, c). split; [exact Hin|]. cbn [fst]. apply in_map. apply j8_in. exact Hj.
    - rewrite int_add_small; rewrite ?toZ_of_Z_small by slia; slia.
  Qed.
  Lemma ro_of_rb : forall b, In b (c_rb K) -> iget b RO = Some tt.
  Proof. intros b Hb. unfold RO, ro_of. apply fold_iset_in. unfold ro_bytes. apply in_or_app. right. exact Hb. Qed.
  (* [comment removed for export] *)
  Lemma ro_of_range : forall k u, iget k RO = Some u -> 0x10000 <= to_Z k < 0x311000.
  Proof.
    intros k u Hg. unfold RO, ro_of in Hg. apply fold_iset_inv in Hg. unfold ro_bytes in Hg. apply in_app_or in Hg as [Hg|Hg].
    - apply in_flat_map in Hg as ([a c] & Hin & Hk). cbn [fst] in Hk. apply in_map_iff in Hk as (j & <- & Hj).
      pose proof (HK_ro a c Hin) as (_ & Hlo & Hhi & _). pose proof (in_j8 j Hj). rewrite int_add_small by slia. slia.
    - exact (HK_rb k Hg).
  Qed.

  Lemma rb_addr_dec : forall a, rb_addr a \/ ~ rb_addr a.
  Proof.
    intros a. unfold rb_addr. induction (c_rb K) as [|b l IH]; [right; intros (b & [] & _)|].
    destruct (Z.eq_dec (to_Z b) a) as [E|NE]; [left; exists b; split; [left; reflexivity | exact E]|].
    destruct IH as [(b' & Hb' & E')|IH]; [left; exists b'; split; [right; exact Hb' | exact E']|].
    right. intros (b' & [<-|Hb'] & E'); [exact (NE E') | apply IH; exists b'; split; assumption].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma option_byte_eq_dec : forall (x y : option byte), x = y \/ x <> y.
  Proof.
    intros [x|] [y|]; try (right; discriminate); [|left; reflexivity].
    destruct (Z.eq_dec (bv_unsigned x) (bv_unsigned y)) as [E|NE].
    - left. f_equal. apply bv_eq. exact E.
    - right. intros E. apply NE. injection E as ->. reflexivity.
  Qed.

  Lemma rblock_of_G : forall Q st rho ms mo s LB G g,
    I2RX Q st rho ms mo s LB G -> In g G -> rblock_range (g_addr g) (to_Z (g_size g)).
  Proof.
    intros Q st rho ms mo s LB G g X Hg.
    pose proof (proj1 (Forall_forall _ _) (r_Gin _ _ _ _ _ _ _ _ X) g Hg) as (Hin & _).
    exact (HH_RHEAP_block_range H HH _ _ _ _ (r_heap _ _ _ _ _ _ _ _ X) Hin).
  Qed.

  Lemma adr_wa : forall rho t A z, rho t = wa A -> 0 <= A -> 0 <= z -> A + z < 2 ^ 64 ->
    bv_unsigned (adr rho t z) = A + z.
  Proof.
    intros rho t A z Ht HA Hz Hlt. unfold adr, wa. rewrite Ht, bv_add_unsigned, !Z_to_bv_unsigned.
    unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    rewrite (Z.mod_small A) by slia. rewrite (Z.mod_small z) by slia. apply Z.mod_small. slia.
  Qed.

  Lemma adr_0 : forall rho z, rho 0%uint63 = Z_to_bv 64 0 -> 0 <= z < 2 ^ 64 -> bv_unsigned (adr rho 0%uint63 z) = z.
  Proof. intros rho z H0 Hz. rewrite (adr_wa rho 0%uint63 0 z); [slia | exact H0 | slia | slia | slia]. Qed.

  Theorem seg_sound : forall Q st rho ms mo F' r cnt,
    fx_run IM code RO no_bp 40 (i_F st) = (F', r, cnt) ->
    I2R Q st rho ms mo ->
    cells0_in (f_mem F') ->
    hs_SR H (fun c' => I2R Q (with_F st F') rho (cfg_ms c') (cfg_model c') /\ cfg_model c' = mo) (mkCfg ms mo).
  Proof.
    intros Q st rho ms mo F' r cnt Hrun (s & LB & G & X) Hc0.
    pose proof X as X'.
    destruct X' as [r_Rn0 r_canon0 r_fregs0 r_fcsr0 r_rom0 r_rho2 r_rho3 r_agree0 r_n1 r_heap0 r_krel0 r_mpres0 r_G0 r_Gin0 r_Gnodup0 r_Gtnd0 r_Gnew0 r_Gstk0
                    r_dom0 r_r2 r_r3 r_ro0 r_inb0 r_kinds0 r_cost0 r_cnt0 r_big0 r_stk0 r_lo0 r_auxv0 r_inv0 r_err0 r_LB1 r_LB0h0 r_named1 r_LBsub0 r_frame0].
    destruct (fx_run_pkg rsegs IM code RO Hcode (i_n st) rho no_bp 40 (i_F st) F' r cnt ms ltac:(slia) Hrun r_rho2 r_Rn0 r_ro0 r_canon0)
      as (ms' & Hsteps & Hms & HRn' & _ & Hrom & Hfr & Hfc & Hmrel & Hcell & Hrof & Hro' & Hcan').
    assert (Hag : agree (i_n st) rho rho) by (split; [exact r_rho2 | intros; reflexivity]).
    pose proof (r_Rn0 rho Hag) as HR.
    destruct (fx_run_shape IM code RO rsegs rho r_rho2 Hcode Hnw no_bp 40 (i_F st) F' r cnt ltac:(slia) Hrun ms HR)
      as [(Hinb' & Hdf' & Hku') Hp0]; [split; [exact r_inb0 | split; [intros rg0 H0; destruct r_r2 as (rg0_ & H0_ & _ & _ & Hd & _); congruence | exact r_kinds0]]|].
    pose proof (fx_run_geom IM code RO no_bp 40 (i_F st) F' r cnt Hrun) as Hgeom.
    eapply (sr_evt_k H HH (fun ms'' => ms'' = ms')); [eapply krel_halted; [exact HH | exact r_krel0] | eapply krel_lazy; [exact HH | exact r_krel0] | exists ms'; split; [exact Hms | reflexivity] |].
    intros ms'' ->. apply (sr_done H HH). cbn [cfg_ms cfg_model]. split; [|reflexivity].
    (* [comment removed for export] *)
    set (W := segW Q G).
    assert (HW : munch W (ms_mem ms) (ms_mem ms')).
    { intros x Hout.
      destruct (option_byte_eq_dec (ms_mem ms' x) (ms_mem ms x)) as [E|NE]; [exact E|]. exfalso. apply NE.
      apply Hcell. intros (t & rg & pn & p & ci & Ht & Hp & Hci & j & Hj & Hjlen & Ex).
      unfold W, segW in Hout. rewrite !outside_app in Hout. destruct Hout as (Oxw & Oerr & Ostk & Oblk).
      cbn [outside] in Oerr, Ostk. destruct Oerr as [Oerr _]. destruct Ostk as [Ostk _].
      destruct (iget ci (pg_cells p)) as [c|] eqn:Hc; [|exact (Hci eq_refl)].
      destruct (Hinb' t rg pn p ci c Ht Hp Hc) as (Hlen & Hci512 & _).
      pose proof (i63_range pn). pose proof (i63_range ci).
      pose proof (Hgeom t) as Hgt. rewrite Ht in Hgt.
      destruct (iget t (f_mem (i_F st))) as [rg_|] eqn:E; [| destruct Hgt].
      destruct (r_dom0 t rg_ E) as [-> | [-> | Hblk]].
      - (* [comment removed for export] *)
        destruct r_r2 as (rg0 & Hrg0 & _ & Hlen0 & _). rewrite Hrg0 in E. injection E as <-.
        destruct Hgt as (_ & Hl0 & _). rewrite Hl0, Hlen0 in Hlen, Hjlen.
        destruct (Hc0 rg pn p ci c Ht Hp Hc) as [(xc & Hxin & Hxc) | [Herr | (cc & Hcc)]].
        + apply (proj1 (outside_map _ _ _) Oxw xc Hxin). cbn [fst snd].
          hk_xw xc Hxin.
          rewrite Ex, (adr_0 rho _ r_rho2) by slia. slia.
        + apply Oerr. hk_err. unfold RERRNO in *.
          rewrite Ex, (adr_0 rho _ r_rho2) by slia. slia.
        + (* [comment removed for export] *)
          exfalso. apply NE. apply Hrof. pose proof (HK_ro _ _ Hcc) as (_ & Hlo & Hhi & _).
          rewrite toZ_of_Z_small in Hlo, Hhi by slia.
          destruct (ro_of_cell _ _ j Hcc Hj) as (k & Hk & Ek). rewrite toZ_of_Z_small in Ek by slia.
          exists k, tt. split; [exact Hk|].
          rewrite Ek. rewrite Ex. apply bv_eq. rewrite (adr_0 rho _ r_rho2) by slia.
          rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). rewrite Z.mod_small by slia. reflexivity.
      - (* [comment removed for export] *)
        destruct r_r3 as (rg1 & Hrg1 & Hlo1 & Hlen1 & _). rewrite Hrg1 in E. injection E as <-.
        destruct Hgt as (_ & Hl & _). rewrite Hl, Hlen1 in Hlen, Hjlen.
        apply Ostk. destruct r_lo0 as (Hh & Hl2 & HB & _). pose proof hceil_pos.
        hk_err. destruct r_stk0 as (_ & Hsp & _).
        rewrite Ex, (adr_wa rho 1%uint63 (q_sp0 Q - to_Z (c_stack K)) _ r_rho3) by slia. slia.
      - (* [comment removed for export] *)
        apply in_map_iff in Hblk as (g & <- & Hg).
        pose proof (proj1 (Forall_forall _ _) r_Gin0 g Hg) as (Hin & Hrg & Hsz & Htg & rgg & Hgg & Hlog & Hleng).
        rewrite Hgg in E. injection E as <-. destruct Hgt as (_ & Hl & _). rewrite Hl, Hleng in Hlen, Hjlen.
        apply (proj1 (outside_map _ _ _) Oblk g Hg). cbn [fst snd].
        pose proof (rblock_of_G _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5). pose proof hceil_lt_2p47.
        rewrite Ex, (adr_wa rho (g_tag g) (g_addr g) _ Hrg) by slia. slia. }
    assert (HWok : Forall (rclient_write_ok LB) W).
    { unfold W, segW. rewrite !Forall_app_iff. split; [|split; [|split]].
      - apply Forall_map. apply Forall_forall. intros c Hc. hk_xw c Hc.
        right. left. cbn [fst snd]. slia.
      - constructor; [|constructor]. right. left. cbn [fst snd]. hk_err.
        unfold RERRNO, RLIBC, RCTX, RSSP_GUARD, RGOT_SSP, RVMLOCK in *. slia.
      - constructor; [|constructor]. left. cbn [fst]. destruct r_lo0 as (Hh & Hl2 & _). slia.
      - apply Forall_map. apply Forall_forall. intros g Hg. right. right. cbn [fst snd].
        exists (g_id g, g_addr g, to_Z (g_size g)). split; [exact (proj1 (proj1 (Forall_forall _ _) r_Gin0 g Hg))|]. cbn [blk_addr RMalloc_iface_stmt.blk_size fst snd]. slia. }
    assert (HWaux : Forall (fun iv : Z * Z => snd iv <= q_B Q /\ (snd iv <= RAUXV_CELL \/ RAUXV_CELL + 8 <= fst iv)) W).
    { destruct r_lo0 as (Hh & Hl2 & HB & _). pose proof hceil_lo. pose proof (i63_range (c_stack K)).
      unfold W, segW. rewrite !Forall_app_iff. split; [|split; [|split]].
      - apply Forall_map. apply Forall_forall. intros c Hc. hk_xw c Hc. cbn [fst snd].
        unfold RAUXV_CELL, RLIBC, RCTX in *. slia.
      - constructor; [|constructor]. cbn [fst snd]. hk_err. unfold RERRNO, RAUXV_CELL in *. slia.
      - constructor; [|constructor]. cbn [fst snd]. unfold RAUXV_CELL. slia.
      - apply Forall_map. apply Forall_forall. intros g Hg. cbn [fst snd].
        pose proof (rblock_of_G _ _ _ _ _ _ _ _ _ X Hg) as (R1 & R2 & R3 & R4 & R5). unfold RAUXV_CELL. slia. }
    destruct Hmrel as (Hwm & Hinv' & Hrd).
    exists s, LB, G.
    cbn [with_F i_F i_n i_blk i_cost i_cnt i_big].
    constructor; cbn [with_F i_F i_n i_blk i_cost i_cnt i_big].
    - exact HRn'.
    - exact Hcan'.
    - rewrite Hfr. exact r_fregs0.
    - rewrite Hfc. exact r_fcsr0.
    - rewrite Hrom. exact r_rom0.
    - exact r_rho2.
    - exact r_rho3.
    - exact r_agree0.
    - exact r_n1.
    - exact (HH_RHEAP_frame H HH s LB _ _ W r_heap0 HW Hwm HWok).
    - exact r_krel0.
    - exact r_mpres0.
    - exact r_G0.
    - (* [comment removed for export] *)
      apply Forall_forall. intros g Hg.
      pose proof (proj1 (Forall_forall _ _) r_Gin0 g Hg) as (Hin & Hrg & Hsz & Htg & rgg & Hgg & Hlog & Hleng).
      repeat (split; [assumption|]).
      specialize (Hgeom (g_tag g)). rewrite Hgg in Hgeom. destruct (iget (g_tag g) (f_mem F')) as [rg'|]; [|destruct Hgeom].
      destruct Hgeom as (Hl1 & Hl2 & _). exists rg'. split; [reflexivity|]. split; congruence.
    - exact r_Gnodup0.
    - exact r_Gtnd0.
    - exact r_Gnew0.
    - (* [comment removed for export] *) apply Forall_forall. intros g Hg. apply (mrel_stk rsegs _ _ _ _ (conj Hwm (conj Hinv' Hrd))).
      exact (proj1 (Forall_forall _ _) r_Gstk0 g Hg).
    - (* [comment removed for export] *) intros t rg Ht. specialize (Hgeom t). rewrite Ht in Hgeom.
      destruct (iget t (f_mem (i_F st))) as [rg_|] eqn:E; [|destruct Hgeom]. exact (r_dom0 t rg_ E).
    - (* [comment removed for export] *) destruct r_r2 as (rg0 & Hrg0 & Hlo0 & Hlen0 & Hd0 & Hpg0).
      pose proof (Hgeom 0%uint63) as Hg0. rewrite Hrg0 in Hg0. destruct (iget 0%uint63 (f_mem F')) as [rg0'|] eqn:E0; [|destruct Hg0].
      destruct Hg0 as (Hl1 & Hl2 & _ & Hd1 & _).
      exists rg0'. split; [reflexivity|]. split; [congruence|]. split; [congruence|]. split; [congruence|].
      intros pn p' Hp'. destruct (Hp0 rg0' E0) as (rg0_ & H0_ & Hsub). rewrite Hrg0 in H0_. injection H0_ as <-.
      destruct (Hsub pn p' Hp') as (p & Hp & Hk). destruct (Hpg0 pn p Hp) as [Hw Hkd]. split; [exact Hw | congruence].
    - (* [comment removed for export] *) destruct r_r3 as (rg1 & Hrg1 & Hlo1 & Hlen1 & Hd1).
      pose proof (Hgeom 1%uint63) as Hg1. rewrite Hrg1 in Hg1. destruct (iget 1%uint63 (f_mem F')) as [rg1'|] eqn:E1; [|destruct Hg1].
      destruct Hg1 as (Hl1 & Hl2 & _ & Hd2 & _). exists rg1'. split; [reflexivity|]. repeat split; congruence.
    - exact Hro'.
    - exact Hinb'.
    - exact Hku'.
    - exact r_cost0.
    - exact r_cnt0.
    - exact r_big0.
    - (* [comment removed for export] *) exact (mrel_stk rsegs _ _ _ _ (conj Hwm (conj Hinv' Hrd)) r_stk0).
    - exact r_lo0.
    - (* [comment removed for export] *) exact (HH_rauxv_frame H HH _ _ (q_B Q) W r_auxv0 HW Hwm HWaux).
    - (* [comment removed for export] *) exact (Hinv' r_inv0).
    - (* [comment removed for export] *) exact (mrel_stk rsegs _ _ _ _ (conj Hwm (conj Hinv' Hrd)) r_err0).
    - exact r_LB1.
    - exact r_LB0h0.
    - exact r_named1.
    - exact r_LBsub0.
    - (* [comment removed for export] *) intros a Ha Hcl Hna Hnx Hne. rewrite <- (r_frame0 a Ha Hcl Hna Hnx Hne).
      destruct (rb_addr_dec a) as [(b & Hb & Eb) | Hnrb].
      { (* [comment removed for export] *)
        apply Hrof. exists b, tt. split; [exact (ro_of_rb b Hb)|]. rewrite Eb. reflexivity. }
      apply HW.
      rewrite wa_unsigned by slia. unfold W, segW. rewrite !outside_app. split; [|split; [|split]].
      + apply outside_map. intros c Hc. cbn [fst snd]. intros Hin. apply Hnx. split; [exists c; split; [exact Hc | slia] | exact Hnrb].
      + cbn [outside]. split; [|exact I]. intros Hin. apply Hne. split; [exact Hin | exact Hnrb].
      + cbn [outside]. split; [|exact I]. destruct r_lo0 as (Hh & Hl2 & _). pose proof hceil_lo.
        unfold client0, rclient_addr, ralloc_static in Hcl.
        destruct Hcl as [Hsp | [[Hst _] | (b & Hb & Hr)]]; [slia | slia |].
        pose proof (r_LB0h0 b Hb). slia.
      + apply outside_map. intros g Hg. cbn [fst snd].
        destruct (proj1 (Forall_forall _ _) r_Gnew0 g Hg) as [Hn | [Hd _]].
        * intros Hr. apply Hna. exists g. split; [exact Hn | exact Hr].
        * exact (Hd a Hcl Hna).
  Qed.
End Inv.
