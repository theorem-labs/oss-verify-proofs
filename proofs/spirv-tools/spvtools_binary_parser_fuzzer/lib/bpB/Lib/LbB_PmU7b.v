(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_FKit LbB_MILB LbB_PrsStmt LbB_Own LbB_PmBase LbB_FSlots LbB_PmOwn LbB_PmCut LbB_PmTac LbB_PmHdr LbB_PmCall LbB_PmXp LbB_PmExit LbB_PmFin LbB_DiagStmt LbB_PmDS LbB_PmGlue.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmU3XK LbB_PmU7K LbB_PmU7a LbB_TablImg LbB_RwKit LbB_PmWG.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsGrammar.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablData TablGrammar TablRep TablFacts.

Definition RT_PM_U7_3_1 : list (reg * expr) := [(1%bv, ELit 999492); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 4000)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U7_3_3 : list (reg * expr) := [(1%bv, ELit 999868); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, EAlu ALU_ADD (EVar 33) (ELit 4496)); (11%bv, EAlu ALU_ADD (EVar 32) (ELit 264)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 4000)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U7_4_1 : list (reg * expr) := [(2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (10%bv, ELit 0); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 4000)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_S7G : list (reg * expr) := rt_keep RT_PM_U7_2_1 ++ [(10%bv, ELit 0)].
Definition RT_S7H : list (reg * expr) := rt_keepK V4_KEPT RT_PM_U7_3_3.

Definition log_wins (lg : list sentry) : list (expr * Z * Z) :=
  map (fun se => (a_base (e_addr se), a_off (e_addr se), a_off (e_addr se) + Z.of_nat (e_width se))) lg.

Fixpoint log_idx (b : expr) (off : Z) (lg : list sentry) : nat :=
  match lg with
  | [] => O
  | se :: t => if (expr_eqb (a_base (e_addr se)) b && Z.eqb (a_off (e_addr se)) off)%bool then O else S (log_idx b off t)
  end.

Lemma wr_at_in : forall m a n k j, wr_at asegs m a n -> 0 <= k -> k + j <= n -> 0 <= j -> wr_at asegs m (a + k) j.
Proof.
  intros m a n k j (W0 & W1 & W) Hk Hkj Hj. split; [lia|]. split; [lia|]. intros i Hi.
  replace (a + k + i) with (a + (k + i)) by lia. apply W. lia.
Qed.

Ltac stop_of K :=
  lazymatch type of K with
  | context [MS _ _ (Z_to_bv 64 ?p) _ None _ (seg_rom asegs)] => p
  end.

Ltac run_mem X M :=
  lazymatch type of X with PMXAT _ _ _ _ _ _ ?mm _ _ _ _ _ _ _ => set (M := mm) in * end.
Ltac run_pc VIS p :=
  lazymatch type of VIS with context [s_pc ?SS] => replace (s_pc SS) with p in VIS by reflexivity end.

Ltac keep_regs_by t :=
  let rr := fresh "rr" in let Hrr := fresh "Hrr" in
  intros rr Hrr; cbn in Hrr;
  repeat (destruct Hrr as [<-|Hrr]; [t |]); contradiction.
Ltac keep_regs HR := keep_regs_by ltac:(rewrite (HR _); reflexivity).

Ltac via R' HR :=
  lazymatch goal with |- PropExec.getr _ ?r = _ => transitivity (PropExec.getr R' r); [rewrite (HR r); reflexivity |] end.
Ltac keep_leaf KEEP :=
  lazymatch goal with |- PropExec.getr _ ?r = _ => rewrite (KEEP r ltac:(inb)) end.

Ltac ffk_ex := first [apply Exists_cons_hd; cbn [fst snd]; lia | apply Exists_cons_tl; ffk_ex].
Ltac ffk_close :=
  repeat (apply Forall_cons;
          [cbn [fst snd]; first [left; lia | right; left; lia | right; right; ffk_ex] |]);
  apply Forall_nil.

Lemma ev_u : forall E (n : N) x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 64 -> bv_unsigned (edenot E (EVar n)) = x.
Proof. intros E n x Hx Hr. rewrite Hx, Z_to_bv_unsigned, bv_wrap64_mod. apply Z.mod_small. exact Hr. Qed.

Ltac ffk_run H w OK Hlf :=
  lazymatch goal with |- ffkeepX _ _ ?m (mem_denot ?E ?m (s_log ?SS)) =>
  lazymatch E with Eseed ?R (wenv_vals _ ++ ?Xs) =>
    let HE := constr:(env_world_seed H w R Xs) in
    let W := eval vm_compute in (log_wins (s_log SS)) in
    let MU := fresh "MU" in let EF := fresh "EF" in
    let E32 := fresh "E32" in let E33 := fresh "E33" in let E34 := fresh "E34" in let E35 := fresh "E35" in
    let BND := fresh "BND" in let G := fresh "G" in let G6 := fresh "G6" in
    pose proof (munch_sym E m (s_log SS) W Hlf ltac:(vm_compute; reflexivity)) as MU;
    cbn [num_wins map] in MU;
    pose proof (ev_ff H w E OK HE) as EF; change (EVar WV_FF) with (EVar 33%N) in EF;
    destruct (ev_world_all H w E HE) as (E32 & E33 & E34 & E35 & _);
    pose proof (pmw_bounds H w OK) as BND;
    pose proof (pm_geom H w OK) as G; cbn zeta in G;
    destruct G as (? & ? & ? & ? & ? & G6 & ? & ? & ? & ? & ? & ? & ?);
    rewrite ?(srl3_val _ (EVar 33) (wa_ff w) E33 ltac:(lia)) in MU;
    rewrite ?EF, ?(ev_u _ _ _ E32 ltac:(lia)), ?(ev_u _ _ _ E34 ltac:(lia)), ?(ev_u _ _ _ E35 ltac:(lia)) in MU;
    apply (ffkeepX_munch w _ _ _ _ MU (wmono_mem_denot _ _ _));
    unfold SHBASE in *;
    destruct G6 as [G6|G6]; ffk_close
  end end.

Ltac rwc_ff H w OK Hlf XA :=
  lazymatch goal with |- rw_cells _ (mem_denot ?E ?m (s_log ?SS)) (wa_ff w + ?off) [?c] =>
  lazymatch E with Eseed ?R (wenv_vals _ ++ ?Xs) =>
    let k := eval vm_compute in (log_idx (EVar 33%N) off (s_log SS)) in
    let se := eval vm_compute in (nth_error (s_log SS) k) in
    lazymatch se with Some (SE _ ?wd ?v) =>
    let fs := eval vm_compute in (fsz PM_FCLASS) in
    let EF := fresh "EF" in
    pose proof (ev_ff H w E OK (env_world_seed H w R Xs)) as EF; change (EVar WV_FF) with (EVar 33%N) in EF;
    eapply (rw_cells_log_nth_sb E m (s_log SS) k (EVar 33%N) off wd v _ c);
      [ exact Hlf | vm_compute; reflexivity | vm_compute; reflexivity | rewrite EF; reflexivity
      | apply (wr_at_in _ _ _ _ _ (xa_fwr _ _ _ _ _ _ _ _ _ _ _ _ _ _ XA)); try change (fsz PM_FCLASS) with fs; lia
      | reflexivity | exact Logic.I | try reflexivity ];
    clear EF
    end end end.
Section U7b.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHbp : asan_rt_hyps_bp H.
  Variable LINV : mem -> Prop.
  Hypothesis LINV_frame : forall m m' W, LINV m -> munch W m m' -> wmono asegs m m' ->
    Forall (fun iv : Z * Z => AIMG_TOP <= fst iv) W -> LINV m'.
  Variable ds_repA : list block -> mem -> Z -> Z -> Z -> list block -> Prop.
  Hypothesis DSL : ds_rep_lawsA LINV ds_repA.
  Hypothesis HCTOR : ds_ctor_stmtA H LINV ds_repA.
  Hypothesis HCSEQ : put_cseq_stmtA H LINV ds_repA.
  Hypothesis HDTOR : ds_dtor_stmtA H LINV ds_repA.
  Hypothesis HTL : tabl_leavesA.

  Lemma HHm : asan_rt_hyps H.
Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTLbAPmU7b_0 : list (Z * expr) := [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].
  Lemma pm_u7_3 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (d op : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 17; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf38d0) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S7G -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 4000) [C8 (Z_to_bv 64 d)] ->
    idescA d op ->
    (forall l, g_op TG op = Some l -> 3 <= Zlen l) ->
    (forall msF1 mo1 m1 R1 (sp_p : Z) (l : list Z), as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_PUSH_TYPES) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 17; 19; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_PM_U7_3_3 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf41bc -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 (wa_ff w + 4496) -> PropExec.getr R1 11%bv = Z_to_bv 64 (wa_p w + 264) -> rw_cells asegs m1 (wa_ff w + 4496) [C8 (Z_to_bv 64 (sp_p + 8)); C8 (Z_to_bv 64 (Zlen l - 2))] -> g_op TG op = Some l -> spanA sp_p l -> ffkeepX w [(4496, 16)] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc d op Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 CD ID HL3 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    destruct (idescA_facts d op ID) as (rI & _ & _ & _ & D1 & D2 & D3 & D4 & _).
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 d])) m [KWord (SA (EVar WV_FF) 4000) 8 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 d])) OK (env_world_seed H w R [Z_to_bv 64 d])) as EF.
      assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 d])) (EVar 41) = Z_to_bv 64 d) by reflexivity.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + 4000) _ 0%nat (C8 (Z_to_bv 64 d)));
        [ exact CD | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity ]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 d]
          [KWord (SA (EVar WV_FF) 4000) 8 (EVar 41)] HK1 80%nat [AT_IDESC_OPERANDS] [true; true] 42%N
          [3; 4; 17; 19; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU7b_0 (@nil (Z * expr)) RT_PM_U7_3_1.
    { assert (EV41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 d])) (EVar 41) = Z_to_bv 64 d) by reflexivity.
      split_scs. all: cbn [sc_denot edenot].
      all: change (ev (Eseed R (wenv_vals w ++ [Z_to_bv 64 d])) 41) with (edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 d])) (EVar 41)).
      all: rewrite EV41; wnormB.
      - change 3 with (Z.ones 2). rewrite Z.land_ones by lia. rewrite br_eq by dlia. bool_dlia.
      - rewrite br_ne by dlia. bool_dlia. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    run_mem X1 M1. run_pc VIS1 AT_IDESC_OPERANDS.
    assert (FK1 : ffkeepX w [] m M1) by (subst M1; ffk_run H w OK Hlf1).
    eapply (pm_leaf0 H HHm LINV LINV_frame AT_IDESC_OPERANDS _ _ _ _ (tla_idesc_operands HTL) (d, op)
              w _ _ _ _ _ c _ _ _ _ _ msF1 R1 F fc _ Q);
      [ exact OK | exact X1 | exact KR1 | exact VIS1 | exact RF1 | rtf HTx1 | rtf HTx1 | reflexivity | lia
      | unfold TL_STACK; lia | reflexivity | cbn beta iota; split; [exact ID | rewrite (HR1 10%bv); reflexivity]
      | vm_compute; reflexivity | vm_compute; reflexivity | ].
    intros msF2 mo2 M2 R2 KR2 VIS2 RF2 X2 KEEP2 MU2 WM2 (sp_p & l & GX & SP & E10 & E11).
    pose proof (HL3 l GX) as L3.
    pose proof SP as SPx. unfold spanA in SPx. destruct SPx as (SP1 & SP2 & _).
    assert (FK2 : ffkeepX w [] M1 M2).
    { apply (ffkeepX_munch w [] _ _ _ MU2 WM2). apply Forall_cons; [| apply Forall_nil].
      cbn [fst snd]. left. unfold TL_STACK. lia. }
    pose proof (regs_tbl_restrict w [] _ R2 (rt_keep RT_PM_U7_3_1) (regs_keep w _ R1 R2 RT_PM_U7_3_1 HTx1 KEEP2)
                  ltac:(vm_compute; reflexivity)) as HT2.
    assert (HK2 : know_ok asegs (Eseed R2 (wenv_vals w ++ [])) M2 [KRange (EVar 11) 3 (2 ^ 32)]).
    { apply Forall_cons; [| apply Forall_nil]. cbn [kentry_ok].
      change (edenot (Eseed R2 (wenv_vals w ++ [])) (EVar 11)) with (PropExec.getr R2 11%bv).
      rewrite E11, Z_to_bv_unsigned, bv_wrap64_mod. rewrite Z.mod_small by lia. lia. }
    let p := stop_of K in
    pm_goX HHm LINV_frame OK X2 KR2 VIS2 RF2 HT2 (@nil word) [KRange (EVar 11) 3 (2 ^ 32)] HK2 60%nat [p] [true] 41%N
          [3; 4; 17; 19; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU7b_0 (@nil (Z * expr)) RT_PM_U7_3_3.
    { assert (EV10 : edenot (Eseed R2 (wenv_vals w ++ [])) (EVar 10) = Z_to_bv 64 sp_p) by exact E10.
      split_scs. cbn [sc_denot edenot].
      change (ev (Eseed R2 (wenv_vals w ++ [])) 10) with (edenot (Eseed R2 (wenv_vals w ++ [])) (EVar 10)). rewrite EV10. wnormB.
      rewrite br_geu by dlia. bool_dlia. }
    intros msF3 mo3 R3 KR3 VIS3 RF3 X3 HTx3 HR3 Hlf3.
    run_mem X3 M3. let p := stop_of K in run_pc VIS3 p.
    assert (FK3 : ffkeepX w [(4496, 16)] M2 M3) by (subst M3; ffk_run H w OK Hlf3).
    assert (C4496 : rw_cells asegs M3 (wa_ff w + 4496) [C8 (Z_to_bv 64 (sp_p + 8)); C8 (Z_to_bv 64 (Zlen l - 2))]).
    { change [C8 (Z_to_bv 64 (sp_p + 8)); C8 (Z_to_bv 64 (Zlen l - 2))]
        with ([C8 (Z_to_bv 64 (sp_p + 8))] ++ [C8 (Z_to_bv 64 (Zlen l - 2))]).
      apply rw_cells_appA; split.
      - subst M3; rwc_ff H w OK Hlf3 X2. rewrite (ev_add (Eseed R2 (wenv_vals w ++ [])) 10%N sp_p 8 E10 ltac:(lia) ltac:(lia)). reflexivity.
      - replace (wa_ff w + 4496 + Z.of_nat (cells_size [C8 (Z_to_bv 64 (sp_p + 8))])) with (wa_ff w + 4504) by (cbn; lia).
        subst M3; rwc_ff H w OK Hlf3 X2. rewrite (ev_add (Eseed R2 (wenv_vals w ++ [])) 11%N (Zlen l) (-2) E11 ltac:(lia) ltac:(lia)). replace (Zlen l + -2) with (Zlen l - 2) by lia. reflexivity. }
    assert (FK : ffkeepX w [(4496, 16)] m M3).
    { eapply (ffkeepX_trans w [] [(4496, 16)] _ m M2 M3); [| exact FK3 | apply incl_nil_l | apply incl_refl].
      eapply (ffkeepX_trans w [] [] _ m M1 M2); [exact FK1 | exact FK2 | apply incl_nil_l | apply incl_nil_l]. }
    eapply (K msF3 mo3 M3 R3 sp_p l KR3 VIS3 RF3 X3 HTx3);
      [ via R2 HR3; keep_leaf KEEP2; rewrite (HR1 3%bv); exact G3_0
      | via R2 HR3; keep_leaf KEEP2; rewrite (HR1 4%bv); exact G4_0
      | rtf HTx3 | rtf HTx3 | rtf HTx3 | rtf HTx3
      | exact C4496 | exact GX | exact SP | exact FK
      | keep_regs_by ltac:(via R2 HR3; keep_leaf KEEP2; rewrite (HR1 _); reflexivity) ].
  Qed.

  Lemma pm_u7_4 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 17; 19; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf41bc) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_S7H -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 OL_PUSHK) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c S_OPER TBL_EEF44 [] -> regs_tbl w R1 RT_PUSHK -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> (forall r : reg, In r [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 r = PropExec.getr R r) -> ffkeepX w [] m m1 -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 K.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    let p := stop_of K in
    pm_go HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 (@nil word) (@nil kentry) 20%nat [p] (@nil bool) 41%N
          [3; 4; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTLbAPmU7b_0 (@nil (Z * expr)) RT_PM_U7_4_1.
    { split_scs. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    run_mem X1 M1. let p := stop_of K in run_pc VIS1 p.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U7_4_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    assert (FK : ffkeepX w [] m M1) by (subst M1; ffk_run H w OK Hlf1).
    eapply (K msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 (regs_tbl_sub w [] R1 _ RT_PUSHK HT1 ltac:(vm_compute; reflexivity)));
      [ rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | keep_regs HR1 | exact FK ].
  Qed.

End U7b.
