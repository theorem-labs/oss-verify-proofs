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

From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_DStat LbB_TablStmt LbB_PmLH LbB_PmU2K LbB_PmOL LbB_PmLeaf LbB_PmU3XK LbB_RwKit.

Definition RT_PM_U3X_1_1 : list (reg * expr) := [(1%bv, ELit 992848); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (12%bv, EAlu ALU_ADD (EVar 33) (ELit 2976)); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3X_2_1 : list (reg * expr) := [(1%bv, ELit 992880); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].
Definition RT_PM_U3X_2_2 : list (reg * expr) := [(1%bv, ELit 996888); (2%bv, EVar 35); (8%bv, EVar 34); (9%bv, EVar 35); (19%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (20%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit 2147450880)); (23%bv, EVar 32); (24%bv, EAlu ALU_ADD (EVar 33) (ELit 7984)); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 112)); (27%bv, ELit 18446744073709551608)].

Definition RT_X2 : list (reg * expr) := rt_keep RT_PM_U3X_1_1.

Definition RT_X3 : list (reg * expr) := rt_keep RT_PM_U3X_2_1.

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

Lemma ev_satsub2 : forall E (r : N) n, edenot E (EVar r) = Z_to_bv 64 n -> 2 <= n < 2 ^ 64 ->
  edenot E (EAlu ALU_AND (EAlu ALU_ADD (EAlu ALU_SLTU (EVar r) (EAlu ALU_ADD (EVar r) (ELit (-2)))) (ELit (-1)))
                         (EAlu ALU_ADD (EVar r) (ELit (-2)))) = Z_to_bv 64 (n - 2).
Proof.
  intros E r n Hr Hn. cbn [edenot]. change (ev E r) with (edenot E (EVar r)). rewrite Hr.
  rewrite (w_addm n (-2)) by lia. replace (n + -2) with (n - 2) by lia.
  assert (S0 : alu64 ALU_SLTU (Z_to_bv 64 n) (Z_to_bv 64 (n - 2)) = Z_to_bv 64 0).
  { apply bv_eq. rewrite u_sltu64, !u64_of_Z by lia.
    destruct (n <? n - 2) eqn:L; [apply Z.ltb_lt in L; lia | reflexivity]. }
  rewrite S0.
  assert (M1 : alu64 ALU_ADD (Z_to_bv 64 0) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1)).
  { apply bv_eq. cbn [alu64 alu]. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. reflexivity. }
  rewrite M1, (w_and (2 ^ 64 - 1) (n - 2)) by lia. f_equal.
  rewrite Z.land_comm. change (2 ^ 64 - 1) with (Z.ones 64). rewrite Z.land_ones by lia. apply Z.mod_small. lia.
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

Lemma sc_u3x_ge0 : forall SEGS M E (n : N) x, edenot E (EVar n) = Z_to_bv 64 x -> 0 <= x < 2 ^ 31 ->
  sc_denot SEGS M E (SCBr true BC_GE (EExt true 0 4 (EVar n)) (ELit 0)).
Proof.
  intros SEGS M E n x Hn Hx. cbn [sc_denot edenot]. change (ev E n) with (edenot E (EVar n)). rewrite Hn.
  rewrite ext_sx4_small by lia. rewrite br_geB by lia. destruct (Z.ltb_spec x 0); [lia | reflexivity].
Qed.

Lemma sc_u3x_nez : forall SEGS M E (n : N) r, edenot E (EVar n) = Z_to_bv 64 r -> r mod 2 ^ 64 = 0 ->
  sc_denot SEGS M E (SCBr false BC_NE (EVar n) (ELit 0)).
Proof.
  intros SEGS M E n r Hn Hr. cbn [sc_denot edenot]. change (ev E n) with (edenot E (EVar n)). rewrite Hn.
  replace (Z_to_bv 64 r) with (Z_to_bv 64 0)
    by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); rewrite Hr; reflexivity).
  vm_compute. reflexivity.
Qed.

Lemma sc_u3x_nenz : forall SEGS M E (n : N) r, edenot E (EVar n) = Z_to_bv 64 r -> r mod 2 ^ 64 <> 0 ->
  sc_denot SEGS M E (SCBr true BC_NE (EVar n) (ELit 0)).
Proof.
  intros SEGS M E n r Hn Hr. cbn [sc_denot edenot]. change (ev E n) with (edenot E (EVar n)). rewrite Hn.
  replace (Z_to_bv 64 r) with (Z_to_bv 64 (r mod 2 ^ 64))
    by (apply bv_eq; rewrite !Z_to_bv_unsigned; unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64); apply Z.mod_mod; lia).
  rewrite br_ne by (pose proof (Z.mod_pos_bound r (2 ^ 64) ltac:(lia)); lia).
  destruct (Z.eqb_spec (r mod 2 ^ 64) 0); [contradiction | reflexivity].
Qed.

Lemma sc_u3x_al4 : forall SEGS M E (n : N) d, edenot E (EVar n) = Z_to_bv 64 d -> 0 <= d < 2 ^ 64 -> d mod 4 = 0 ->
  sc_denot SEGS M E (SCBr true BC_EQ (EAlu ALU_AND (EVar n) (ELit 3)) (ELit 0)).
Proof.
  intros SEGS M E n d Hn Hd Hal. cbn [sc_denot edenot]. change (ev E n) with (edenot E (EVar n)). rewrite Hn.
  rewrite w_and by lia. rewrite land_3, Hal. reflexivity.
Qed.

Section U3Xa.
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

  Lemma HHm : asan_rt_hyps H. Proof. exact (proj1 HHbp). Qed.

#[local] Definition HTbAPmU3Xa_0 : list (Z * expr) := [(32, EAlu ALU_ADD (EVar 33) (ELit 5472)); (40, EAlu ALU_ADD (EVar 33) (ELit 4496)); (48, EAlu ALU_ADD (EVar 33) (ELit 2048)); (56, EAlu ALU_ADD (EVar 33) (ELit 4032)); (64, EAlu ALU_ADD (EVar 33) (ELit 3056)); (72, EAlu ALU_ADD (EVar 33) (ELit 3008)); (80, EAlu ALU_ADD (EVar 33) (ELit 5008)); (88, EAlu ALU_ADD (EVar 33) (ELit 32)); (96, EAlu ALU_ADD (EVar 33) (ELit 4000)); (104, ELit 65535); (112, EAlu ALU_ADD (EVar 33) (ELit 6000)); (120, EAlu ALU_ADD (EVar 33) (ELit 6464)); (128, EAlu ALU_ADD (EVar 33) (ELit 7952)); (136, EAlu ALU_ADD (EVar 33) (ELit 3024)); (144, EAlu ALU_ADD (EVar 33) (ELit 656)); (152, EAlu ALU_ADD (EVar 33) (ELit 192)); (160, EAlu ALU_ADD (EVar 33) (ELit 1120)); (168, EAlu ALU_ADD (EVar 33) (ELit 3520)); (176, ELit 262140); (184, EAlu ALU_ADD (EVar 32) (ELit 176)); (192, EAlu ALU_ADD (EVar 33) (ELit 5937)); (200, EAlu ALU_ADD (EVar 33) (ELit 4544)); (208, EAlu ALU_ADD (EVar 33) (ELit 2512)); (216, EAlu ALU_ADD (EVar 33) (ELit 1584)); (224, EAlu ALU_ADD (EVar 33) (ELit 3536)); (232, EAlu ALU_ADD (EVar 33) (ELit 8576)); (240, EAlu ALU_ADD (EVar 33) (ELit 7456)); (248, EAlu ALU_ADD (EVar 33) (ELit 4528)); (256, EAlu ALU_ADD (EVar 33) (ELit 7488)); (264, EAlu ALU_ADD (EVar 33) (ELit 10640)); (272, EAlu ALU_ADD (EVar 32) (ELit 96)); (280, EAlu ALU_ADD (EVar 33) (ELit 9056)); (288, EAlu ALU_ADD (EVar 33) (ELit 11104)); (296, EAlu ALU_ADD (EVar 33) (ELit 8544)); (304, EAlu ALU_ADD (EVar 33) (ELit 9060)); (312, EAlu ALU_ADD (EVar 33) (ELit 2976)); (320, EAlu ALU_ADD (EVar 33) (ELit 5936)); (328, EAlu ALU_ADD (EVar 33) (ELit 10176)); (336, EAlu ALU_ADD (EVar 33) (ELit 8512)); (344, EAlu ALU_ADD (EVar 33) (ELit 8016)); (352, EAlu ALU_ADD (EVar 33) (ELit 7424)); (360, EAlu ALU_ADD (EVar 32) (ELit 92)); (368, EAlu ALU_ADD (EVar 32) (ELit 93)); (376, EAlu ALU_ADD (EVar 32) (ELit 40)); (384, EAlu ALU_ADD (EVar 33) (ELit 6928)); (392, EAlu ALU_ADD (EVar 33) (ELit 6960)); (400, EAlu ALU_ADD (EVar 33) (ELit 9616)); (408, EAlu ALU_ADD (EVar 32) (ELit 216)); (416, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 216)) (ELit 3)) (ELit 2147450880)); (424, EAlu ALU_ADD (EVar 33) (ELit 96)); (432, EAlu ALU_ADD (EVar 32) (ELit 232)); (440, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 232)) (ELit 3)) (ELit 2147450880)); (448, EAlu ALU_ADD (EVar 32) (ELit 224)); (456, EAlu ALU_ADD (EVar 33) (ELit 64)); (464, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 224)) (ELit 3)) (ELit 2147450880)); (472, EAlu ALU_ADD (EVar 33) (ELit 176)); (480, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 240)) (ELit 3)) (ELit 2147450880)); (488, EAlu ALU_ADD (EVar 33) (ELit 8480)); (496, EAlu ALU_ADD (EVar 33) (ELit 10112)); (504, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 264)) (ELit 3)) (ELit 2147450880)); (512, EAlu ALU_ADD (EVar 32) (ELit 88)); (520, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 88)) (ELit 3)) (ELit 2147450880)); (528, EAlu ALU_ADD (EVar 32) (ELit 48)); (536, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 48)) (ELit 3)) (ELit 2147450880)); (544, ELit 2305843009213693952); (552, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 272)) (ELit 3)) (ELit 2147450880)); (560, EAlu ALU_ADD (EVar 32) (ELit 240)); (568, EVar 33); (576, EVar 33); (584, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 56)) (ELit 3)) (ELit 2147450880)); (592, EAlu ALU_ADD (EVar 32) (ELit 56)); (600, EAlu ALU_ADD (EVar 32) (ELit 272)); (608, EAlu ALU_ADD (EVar 33) (ELit 9050)); (616, ELit 2147450880); (624, EAlu ALU_ADD (EVar 33) (ELit 9040)); (632, EAlu ALU_ADD (EVar 32) (ELit 264)); (640, EAlu ALU_ADD (EVar 33) (ELit 9136)); (648, EVar 32); (656, EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 32) (ELit 72)) (ELit 3)) (ELit 2147450880)); (664, EAlu ALU_ADD (EVar 32) (ELit 72)); (680, EVar 33); (688, EAlu ALU_ADD (EVar 33) (ELit 10112)); (696, EAlu ALU_ADD (EVar 33) (ELit 9136)); (704, EVar 32); (712, EAlu ALU_ADD (EVar 33) (ELit 9120)); (720, EAlu ALU_ADD (EVar 33) (ELit 9040))].
  Lemma pm_u3x_1 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (ext wv : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2628) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_ARM -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 9052) [C4 (Z_to_bv 64 ext)] ->
    0 <= ext < 2 ^ 31 ->
    PropExec.getr R 21%bv = Z_to_bv 64 (sx32A wv) ->
    0 <= wv < 2 ^ 32 ->
    (forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_LOOKUP_EXT) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 11; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_PM_U3X_1_1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf2650 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 ext -> PropExec.getr R1 11%bv = Z_to_bv 64 (sx32A wv) -> PropExec.getr R1 12%bv = Z_to_bv 64 (wa_ff w + 2976) -> rw_cells asegs m1 (wa_ff w + 2976) [C8 (Z_to_bv 64 0)] -> ffkeepX w [(2976, 8)] m m1 -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc ext wv Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 CEXT HEXT HX21 HWV K1.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 ext])) (EVar 41) = Z_to_bv 64 ext) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 ext])) m [KWord (SA (EVar WV_FF) 9052) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 ext])) OK (env_world_seed H w R [Z_to_bv 64 ext])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + 9052) _ 0%nat (C4 (Z_to_bv 64 ext)));
        [ exact CEXT | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity ]. }
    pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 ext]
          [KWord (SA (EVar WV_FF) 9052) 4 (EVar 41)] HK1 50%nat [AT_LOOKUP_EXT] [true] 42%N
          [3; 4; 11; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU3Xa_0 (@nil (Z * expr)) RT_PM_U3X_1_1.
    { split_scs; first [ exact (sc_u3x_ge0 _ _ _ _ ext E41 HEXT) ]. }
    intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
    run_mem X1 M1. run_pc VIS1 AT_LOOKUP_EXT.
    pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U3X_1_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
    assert (FK : ffkeepX w [(2976, 8)] m M1) by (subst M1; ffk_run H w OK Hlf1).
    assert (CD : rw_cells asegs M1 (wa_ff w + 2976) [C8 (Z_to_bv 64 0)]) by (subst M1; rwc_ff H w OK Hlf1 X0).
    eapply (K1 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 HT1);
      first [ rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rtf HT1 | exact CD | exact FK
            | (rewrite (HR1 10%bv); apply (eq_trans (y := Z_to_bv 64 (sx32A ext))); [apply (edenot_sext32 _ 41 ext); [reflexivity | lia] | f_equal; unfold sx32A, PrsGrammar.sx32; destruct (Z.ltb_spec ext (2 ^ 31)); lia])
            | (rewrite (HR1 11%bv); apply (eq_trans (y := PropExec.getr R 21%bv)); [reflexivity | exact HX21])
            | keep_regs HR1 ].
  Qed.

  Lemma pm_u3x_2 : forall (w : pmwA H) s LB LBs m mo c msF R F fc (ext r : Z) (Q : config -> Prop),
    pmw_okA H w -> PMXA H LINV w s LB LBs m mo c [3; 4; 11; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> c_tr c = [] ->
    (forall q k, In (q, k) (c_blocks c) -> k <= 2 ^ 40) ->
    as_AKREL H s (mkCfg msF mo) -> as_VIS H s msF = MS R F (Z_to_bv 64 0xf2650) fc None m (seg_rom asegs) -> rfull R ->
    frm_zero fc -> regs_tbl w R RT_X2 -> PropExec.getr R 3%bv = wa_gp w -> PropExec.getr R 4%bv = wa_tp w ->
    rw_cells asegs m (wa_ff w + 9052) [C4 (Z_to_bv 64 ext)] ->
    0 <= ext < 2 ^ 31 ->
    PropExec.getr R 10%bv = Z_to_bv 64 r ->
    (r mod 2 ^ 64 <> 0 -> forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_IS_NONSEMANTIC) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 11; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_PM_U3X_2_1 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf2670 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 ext -> m1 = m -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    (r mod 2 ^ 64 = 0 -> forall msF1 mo1 m1 R1, as_AKREL H s (mkCfg msF1 mo1) -> as_VIS H s msF1 = MS R1 F (Z_to_bv 64 AT_IS_NONSEMANTIC) fc None m1 (seg_rom asegs) -> rfull R1 -> PMXA H LINV w s LB LBs m1 mo1 c [3; 4; 11; 39; 40; 41; 43; 45]%nat TBL_EEF44 [] -> regs_tbl w R1 RT_PM_U3X_2_2 -> PropExec.getr R1 3%bv = wa_gp w -> PropExec.getr R1 4%bv = wa_tp w -> PropExec.getr R1 1%bv = Z_to_bv 64 0xf3618 -> PropExec.getr R1 2%bv = Z_to_bv 64 (wa_s1 w) -> PropExec.getr R1 10%bv = Z_to_bv 64 ext -> m1 = m -> (forall rr : reg, In rr [18%bv; 22%bv; 25%bv] -> PropExec.getr R1 rr = PropExec.getr R rr) -> as_SR H Q (mkCfg msF1 mo1)) ->
    as_SR H Q (mkCfg msF mo).
  Proof.
    intros w s LB LBs m mo c msF R F fc ext r Q OK X0 Htr Hbsz KR0 VIS0 RF0 FZ0 HT0 G3_0 G4_0 CEXT HEXT HX10 K2 K2F.
    pose proof (pm_geom H w OK) as G. cbn zeta in G.
    destruct G as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8 & Q9 & Q10 & Q11 & Q12 & Q13).
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    pose proof (wk_n H w OK) as WN.
    pose proof (pmw_bounds H w OK) as BND.
    assert (E41 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 ext])) (EVar 41) = Z_to_bv 64 ext) by reflexivity.
    assert (HK1 : know_ok asegs (Eseed R (wenv_vals w ++ [Z_to_bv 64 ext])) m [KWord (SA (EVar WV_FF) 9052) 4 (EVar 41)]).
    { pose proof (ev_ff H w (Eseed R (wenv_vals w ++ [Z_to_bv 64 ext])) OK (env_world_seed H w R [Z_to_bv 64 ext])) as EF.
      apply Forall_cons; [| apply Forall_nil].
      eapply (kword_of_rw_cells asegs _ m (wa_ff w + 9052) _ 0%nat (C4 (Z_to_bv 64 ext)));
        [ exact CEXT | reflexivity | reflexivity | lia
        | unfold estart; cbn [a_base a_off]; rewrite EF; cbn [Z.of_nat]; lia
        | cbn [Z.of_nat]; lia | cbn [Z.of_nat]; lia | cbn [cbytes]; rewrite E41; reflexivity ]. }
    assert (E10 : edenot (Eseed R (wenv_vals w ++ [Z_to_bv 64 ext])) (EVar 10) = Z_to_bv 64 r) by exact HX10.
    destruct (Z.eq_dec (r mod 2 ^ 64) 0) as [Hr0 | Hr0].
    -
      pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 ext]
            [KWord (SA (EVar WV_FF) 9052) 4 (EVar 41)] HK1 50%nat [AT_IS_NONSEMANTIC] [false; true] 42%N
            [3; 4; 11; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU3Xa_0 (@nil (Z * expr)) RT_PM_U3X_2_2.
      { split_scs; first [ exact (sc_u3x_ge0 _ _ _ _ ext E41 HEXT) | exact (sc_u3x_nez _ _ _ _ r E10 Hr0) ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      run_mem X1 M1. run_pc VIS1 AT_IS_NONSEMANTIC.
      pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U3X_2_2 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
      eapply (K2F Hr0 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 HT1);
        first [ rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rtf HT1
              | (rewrite (HR1 10%bv); apply (eq_trans (y := Z_to_bv 64 (sx32A ext))); [apply (edenot_sext32 _ 41 ext); [reflexivity | lia] | f_equal; unfold sx32A, PrsGrammar.sx32; destruct (Z.ltb_spec ext (2 ^ 31)); lia])
              | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity)
              | keep_regs HR1 ].
    -
      pm_goX HHm LINV_frame OK X0 KR0 VIS0 RF0 HT0 [Z_to_bv 64 ext]
            [KWord (SA (EVar WV_FF) 9052) 4 (EVar 41)] HK1 50%nat [AT_IS_NONSEMANTIC] [true; true] 42%N
            [3; 4; 11; 39; 40; 41; 43; 45]%nat (@nil Z) (@nil Z) HTbAPmU3Xa_0 (@nil (Z * expr)) RT_PM_U3X_2_1.
      { split_scs; first [ exact (sc_u3x_ge0 _ _ _ _ ext E41 HEXT) | exact (sc_u3x_nenz _ _ _ _ r E10 Hr0) ]. }
      intros msF1 mo1 R1 KR1 VIS1 RF1 X1 HTx1 HR1 Hlf1.
      run_mem X1 M1. run_pc VIS1 AT_IS_NONSEMANTIC.
      pose proof (regs_tbl_restrict w [] _ R1 RT_PM_U3X_2_1 HTx1 ltac:(vm_compute; reflexivity)) as HT1.
      eapply (K2 Hr0 msF1 mo1 M1 R1 KR1 VIS1 RF1 X1 HT1);
        first [ rewrite (HR1 3%bv); exact G3_0 | rewrite (HR1 4%bv); exact G4_0 | rtf HT1
              | (rewrite (HR1 10%bv); apply (eq_trans (y := Z_to_bv 64 (sx32A ext))); [apply (edenot_sext32 _ 41 ext); [reflexivity | lia] | f_equal; unfold sx32A, PrsGrammar.sx32; destruct (Z.ltb_spec ext (2 ^ 31)); lia])
              | (subst M1; replace (s_log SSr) with (@nil sentry) by (vm_compute; reflexivity); reflexivity)
              | keep_regs HR1 ].
  Qed.

End U3Xa.
