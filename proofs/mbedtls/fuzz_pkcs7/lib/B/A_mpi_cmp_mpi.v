(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Arr CellsX HeapIface MpiCoreAux MpiWalkAux ZBridge.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep MpiVal MpiFacts.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.P Require Import P_mpi_cmp.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.B Require Import AImg AImgRT.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BLX Require Import LxA.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXB Require Import LxATac LxAMpiTac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import TacA.   (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Unset Lia Cache.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import FF5. (* [comment removed for export] *)
Local Ltac pqlia ::= ff5_pqlia.
Local Ltac transport_after_call segs m m' MU WM ::= ff5_transport_after_call segs m m' MU WM.
Local Ltac solve_apart ::= ff5_solve_apart.
Local Ltac solve_apart0 ::= ff5_solve_apart0.
Local Ltac solve_disjoint ::= ff5_solve_disjoint.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibB Require Import LiaOrcFF5. (* [comment removed for export] *)
Local Ltac lia_t12 ::= orc_lia_t12. (* [comment removed for export] *)
Local Ltac ff5_rlia ::= orc_ff5_rlia. (* [comment removed for export] *)
Local Ltac ff5_overlap_ctx A2 n2 a len ::= orc_ff5_overlap_ctx A2 n2 a len. (* [comment removed for export] *)
Local Ltac ff5_overlap A2 n2 a len ::= orc_ff5_overlap A2 n2 a len. (* [comment removed for export] *)
Local Ltac qlia ::= orc_qlia. (* [comment removed for export] *)
Local Ltac pqlia ::= orc_ff5_pqlia. (* [comment removed for export] *)
Local Ltac lia1 D ::= orc_lia1 D. (* [comment removed for export] *)
Local Ltac dlia ::= orc_dlia. (* [comment removed for export] *)
Local Ltac plia ::= orc_plia. (* [comment removed for export] *)
Local Ltac clear_disj ::= fc_clear_disj. (* [comment removed for export] *)
Local Ltac prune_disj ::= fc_prune_disj. (* [comment removed for export] *)
Local Ltac clear_mods ::= fc_clear_mods. (* [comment removed for export] *)
Local Ltac keep_disj1 D ::= fc_keep_disj1 D. (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac2 e25kn_keep_near (t : Init.constr) : Init.unit :=
  let seed := FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) t in
  let e := LiaTuning.zf_mkenv () in
  let (ids, _) := List.fold_left (fun acc h =>
      let (ids, cache) := acc in
      let (id, body, ty) := h in
      match body with
      | Init.Some _ => acc
      | Init.None =>
          let (isp, cache) := LiaTuning.zf_is_prop cache ty in
          if isp then
            (if LiaTuning.zf_plain_arith e ty then
               (if FSet.is_empty (FSet.inter seed (FF5.ffn_vars (FSet.empty FSet.Tags.ident_tag) ty))
                then (id :: ids, cache) else (ids, cache))
             else (id :: ids, cache))
          else (ids, cache)
      end) ([], { LiaTuning.zc_c := FMap.empty FSet.Tags.constant_tag; LiaTuning.zc_i := FMap.empty FSet.Tags.inductive_tag })
      (Control.hyps ()) in
  match ids with
  | [] => ()
  | _ :: _ => match Control.case (fun () => Std.clear ids) with
              | Init.Val _ => ()
              | Init.Err _ => List.iter (fun id => match Control.case (fun () => Std.clear [id]) with Init.Val _ => () | Init.Err _ => () end) ids
              end
  end.
Ltac ff_keep_near t ::= let f := ltac2:(t |- e25kn_keep_near (Option.get (Ltac1.to_constr t))) in f t.
Ltac2 gd_tbl_A_mpi_cmp_mpi () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.HeapIface.blk"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_at"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.limb_own"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_own"; "RocqVerifyHarness.AgentSubmission.Spec.Rep.LHeap"; "Stdlib.ZArith.BinInt.Z.lt"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_p"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.al_wf"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.cs_ok"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.abase"; "RocqVerifyHarness.AgentSubmission.LibA.AShadow.aobj"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_addr"; "Stdlib.ZArith.BinInt.Z.le"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.md_n"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "RocqVerifyHarness.AgentSubmission.LibA.AEvtA.evtA"; "mpi_cmp_postA"; "Stdlib.ZArith.BinInt.Z.sgn"; "RocqVerifyHarness.AgentSubmission.Spec.MpiVal.mpd_val"; "RocqVerifyHarness.AgentSubmission.B.AImg.asegs"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.shiftr"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_sb"; "RocqVerifyHarness.AgentSubmission.P.P_mpi_cmp.SIGF"; "Corelib.Init.Logic.not"].


Definition A_MPI_CMP_MPI_E : Z := 0x9d9a4.   (* [comment removed for export] *)
Notation MPI_CMP_MPI_STACK_A := 16 (only parsing).

Definition mpi_cmp_postA (segs : list Segment) (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word)
    (F : bvmap 5 word) (fc : bv 32) (r : Z) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(4.(5.$0.R10.(6.(7.O15.O14.O13.O12.R?.R>.R=.O11.O10.(8.&40.O3.)R<.R;.R:.R9.R8.R7.R6.O?.O>.O=.O<.O;.O:.O9.O8.O7.O6.R5.R4.R3.R2.)O5.(9.O15.)O4.(:.(2.&40.))R1.(;.O16.)))(4.(<.(=.(>.$?.$?.)(10.$?.$?.O2.(11.&40.O14.))(12.(>.$?.$?.)))O1.R1.)(4.(13.O16.O1.R1.)(4.(14.O16.R1.)(15.O16.R1.O2.(11.&40.O14.)))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_cmp_mpi_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_A_mpi_cmp_mpi ()) "PCS,P,$?.SpPra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(16.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PLB,(17.$18.)PdX,$19.PdY,$19.Plo,$?.P,(1:.O3.R5.R4.R3.)P,(1:.O3.R6.R5.R3.)P,P,(5.$1;.(1<.R5.)$1=.)(1>.=(1?.R6.))P,P,(5.$1;.(1<.R5.)$1=.)(1>.=(1?.R6.))P,(14.O3.R9.)P,(20.O2.)P,(21.O2.R2=.)P,(22.O3.O2.R<.)P,(23.O3.O2.R2?.R=.(24.R;.)+10.)P,(23.O3.O2.R30.R>.(24.R;.)+10.)P,P,(25.+1.(26.R=.))(23.O3.O2.R32.R10.(1?.R>.)(27.+4.(26.R>.)))P,P,(25.+1.(26.R=.))(23.O3.O2.R33.R11.(1?.R>.)(27.+4.(26.R>.)))P,(15.O3.R11.R=.(11.&40.R31.))P,(25.=R>.)P,(25.R?.(28.(11.&40.R33.)+10.))P,(5.$?.(29.(11.&40.R34.)+10.)=)P,(2:.R37.R11.(28.(11.&40.R35.)R11.))P,(2;.(25.(2<.(24.R14.)+10.)R12.)(25.(11.&40.R36.)(24.R14.)))P,(2;.(25.(2<.(24.R14.)+10.)R13.)(25.(11.&40.R37.)(24.R14.)))P,P,(25.+1.(26.R16.))(2;.(25.(2<.(1?.R17.)(27.+4.(26.R17.)))R15.)(25.(11.&40.R39.)(1?.R17.)))P,P,(25.+1.(26.R16.))(2;.(25.(2<.(1?.R17.)(27.+4.(26.R17.)))R16.)(25.(11.&40.R3:.)(1?.R17.)))P,(5.(2.&40.)R32.(8.&40.(24.R18.)))P,(5.(2.&40.)R32.(8.&40.(24.R18.)))(2=.O3.O2.R3>.(2>.O3.R3=.R3<.R3;.R3:.R36.R35.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R1>.R1=.(2?.(28.(30.R1:.)(30.R19.)))R18.R1<.)(6.(7.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.)R1>.(8.&40.O1.)R1=.(:.(2.&40.))R1<.(;.O3.)))")
(* [comment removed for export] *).

Lemma bx_sw32_cases : forall w : word,
  0 <= w32 w < 4294967296 /\
  ((w32 w < 2147483648 /\ zswrap 32 (zlow 32 (bv_unsigned w)) = w32 w
     /\ zlow 64 (zswrap 32 (zlow 32 (bv_unsigned w))) = w32 w)
   \/ (2147483648 <= w32 w /\ zswrap 32 (zlow 32 (bv_unsigned w)) = w32 w - 4294967296
     /\ zlow 64 (zswrap 32 (zlow 32 (bv_unsigned w))) = w32 w + 18446744069414584320)).
Proof.
  intros w. change (zlow 32 (bv_unsigned w)) with (w32 w).
  assert (B : 0 <= w32 w < 2^32) by (unfold w32; apply Z.mod_pos_bound; lia).
  destruct (lx_s32_cases (w32 w) B) as [E1 E2]. rewrite E2, E1.
  split; [exact B|]. destruct (Z.ltb_spec (w32 w) (2^31)); [left | right]; lia.
Qed.

Lemma bx_res_cases : forall (sg sg' : Z) (xs ys : list word) (n i n' j : Z),
  (sg = 1 \/ sg = -1) -> (sg' = 1 \/ sg' = -1) -> SIGF xs n i -> SIGF ys n' j ->
  (j < i -> Z.sgn (sg * lval xs n - sg' * lval ys n') = sg) /\
  (i < j -> Z.sgn (sg * lval xs n - sg' * lval ys n') = - sg') /\
  (i = j -> i <> 0 -> sg <> sg' -> Z.sgn (sg * lval xs n - sg' * lval ys n') = sg) /\
  (i = 0 -> j = 0 -> Z.sgn (sg * lval xs n - sg' * lval ys n') = 0).
Proof.
  intros sg sg' xs ys n i n' j HS HS' SX SY.
  pose proof SX as (I1 & I2 & I3). pose proof SY as (J1 & J2 & J3).
  split; [|split; [|split]]; intros.
  - apply sgn_of_lt; [exact HS | exact HS' |].
    pose proof (SIGF_lt xs n i ys n' j SX SY H). pose proof (lval_range ys n' ltac:(lia)). lia.
  - apply sgn_of_gt; [exact HS | exact HS' |].
    pose proof (SIGF_lt ys n' j xs n i SY SX H). pose proof (lval_range xs n ltac:(lia)). lia.
  - subst j. destruct I3 as [I3|I3]; [lia|]. destruct J3 as [J3|J3]; [lia|].
    pose proof (pow32_pos (i - 1) ltac:(lia)). rewrite I2, J2.
    destruct HS as [E|E]; destruct HS' as [E'|E']; subst sg sg'; try lia;
      first [ apply Z.sgn_pos; lia | apply Z.sgn_neg; lia ].
  - subst i j. rewrite I2, J2, !lval_0. rewrite !Z.mul_0_r. reflexivity.
Qed.

Section Walk.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Local Instance lxi : LxImg asegs AL := lxA_img AL IMG.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  (* [comment removed for export] *)
  Variables (m mm : mem) (lo : Z) (junk : list byte).
  Variables (X P n sg : Z) (xs : list word) (pad : word).
  Variables (Y Q n' sg' : Z) (ys : list word) (pad' : word).
  Hypothesis CX : rw_cells asegs mm X [C8 (Z_to_bv 64 P); C2 (Z_to_bv 64 sg); C2 (Z_to_bv 64 n); C4 pad].
  Hypothesis HX : bytes_at asegs mm P (u32s xs).
  Hypothesis LX : Z.of_nat (length xs) = n.
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis SG : sg = 1 \/ sg = -1.
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis PB : n = 0 \/ 0 < P /\ P mod 4 = 0.
  Hypothesis CY : rw_cells asegs mm Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'].
  Hypothesis HY : bytes_at asegs mm Q (u32s ys).
  Hypothesis LY : Z.of_nat (length ys) = n'.
  Hypothesis Hn' : 0 <= n' <= 10000.
  Hypothesis SG' : sg' = 1 \/ sg' = -1.
  Hypothesis YB : 0 <= Y /\ Y + 16 <= 2^64.
  Hypothesis QB : n' = 0 \/ 0 < Q /\ Q mod 4 = 0.
  Hypothesis MI : mem_inv asegs mm.
  Hypothesis ALX : X mod 8 = 0.
  Hypothesis ALY : Y mod 8 = 0.
  Hypothesis X0 : 0 < X.
  Hypothesis Y0 : 0 < Y.
  Hypothesis OX : aobj asegs AL CS mm X 16.
  Hypothesis OY : aobj asegs AL CS mm Y 16.
  Hypothesis OP : 1 <= n -> aobj asegs AL CS mm P (4 * n).
  Hypothesis OQ : 1 <= n' -> aobj asegs AL CS mm Q (4 * n').
  Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis ST : stk asegs mm lo (bv_unsigned sp + -16).
  Hypothesis MU : munch [(lo, bv_unsigned sp)] m mm.
  Hypothesis WM : wmono asegs m mm.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis PBB : 0 <= P /\ P + 4 * n <= 2^64.
  Hypothesis QBB : 0 <= Q /\ Q + 4 * n' <= 2^64.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHY := (Z_to_bv 64 (Z.shiftr Y 3 + al_sb AL)).
  Let POST (T : Z) := mpi_cmp_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc T lo m.
  Notation RES := (Z.sgn (sg * lval xs n - sg' * lval ys n')).

  Ltac al_facts :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
  Ltac a0_of := lazymatch goal with |- context [mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?v) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] => v end.
  Ltac limb_cases w := destruct (bx_sw32_cases w) as [?BW [(?&?&?)|(?&?&?)]].
  Ltac bx_apply L :=
    first [ eapply L | eapply evtA_eq; [ apply lx_MS_regs; apply mkR_eq31 | eapply L ] ].
  Ltac bx_mem :=
    match goal with E : ?mx = mm |- _ => is_var mx; subst mx end;
    repeat match goal with
           | H : (_ =? _) = _ |- _ => clear H
           | H : (_ <? _) = _ |- _ => clear H
           | H : (if _ then _ else _) = _ |- _ => clear H
           end.
  Ltac bx_reg := lazymatch goal with |- @eq (bv _) _ _ => first [ reflexivity | f_equal; lia ] end.

  (* [comment removed for export] *)
  Lemma b_loop3 : forall (k : nat) (r T : Z) (xt2 xa2 xa3 xt3 xt4 xt5 xt6 : word),
    Z.to_nat r = k -> 0 <= r -> r <= n -> r <= n' ->
    T = sg * Z.sgn (lval xs r - lval ys r) ->
    evtA asegs AL CS (POST T)
      (MS (mkR ra SP' gp tp SHY (Z_to_bv 64 sg) xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) xa2 xa3 SB SHX
               (Z_to_bv 64 (4 * r - 4)) (Z_to_bv 64 (r + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9dc88) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros r T xt2 xa2 xa3 xt3 xt4 xt5 xt6 Hk Hr Rn Rn' HT; al_facts.
    - (* [comment removed for export] *)
      assert (r = 0) as -> by (clear - Hk Hr; lia).
      assert (HT0 : T = 0) by (rewrite HT, !lval_0; cbn; lia). rewrite HT0.
      lx_run_tac (PLAN [0x9dc88] [] 40%N); lx_tree.
      all: bx_mem; lx_leaf.
    - assert (N1 : 1 <= r) by (clear - Hk Hr; lia).
      assert (N1x : 1 <= n) by (clear - N1 Rn; lia). assert (N1y : 1 <= n') by (clear - N1 Rn'; lia).
      pose proof (OP N1x) as OPn. pose proof (OQ N1y) as OQn.
      pose proof PB as PB'; destruct PB' as [N0|[PP PAL]]; [exfalso; clear - N0 N1x; lia|].
      pose proof QB as QB'; destruct QB' as [N0|[QP QAL]]; [exfalso; clear - N0 N1y; lia|].
      (* [comment removed for export] *)
      lx_limb HX (r - 1) wx VX. lx_limb HY (r - 1) wy VY.
      lx_run_tac (PLAN [0x9dc88] [(0x9dc08, DJoin); (0x9dc50, DJoin)] 200%N); lx_tree.
      all: bx_mem; clear SG SG' PB QB; limb_cases wx; limb_cases wy.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9dc88) _ _ _ _] =>
               assert (EQ : limb32 xs (Z.to_nat (r - 1)) = limb32 ys (Z.to_nat (r - 1))) by lia;
               bx_apply (IH (r - 1) T);
               [ .. | rewrite HT, (cmp_step_eq xs ys r) by lia; reflexivity ]
           | |- context [mkR _ _ _ _ _ _ _ _ _ (Z_to_bv 64 (- sg)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _] =>
               assert (HV : T = - sg) by (rewrite HT, (cmp_step_lt xs ys r) by lia; lia);
               rewrite HV; lx_leaf
           | |- _ =>
               assert (HV : T = sg) by (rewrite HT, (cmp_step_gt xs ys r) by lia; lia);
               rewrite HV; lx_leaf
           end.
      all: first [ bx_reg | lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma b_decide : forall (i j : Z) (xt2 xa2 xt3 xt4 xt5 xt6 : word),
    SIGF xs n i -> SIGF ys n' j -> ~ (i = 0 /\ j = 0) ->
    evtA asegs AL CS (POST RES)
      (MS (mkR ra SP' gp tp SHY (Z_to_bv 64 j) xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) xa2 (Z_to_bv 64 i) SB SHX
               (Z_to_bv 64 (4 * i - 4)) (Z_to_bv 64 (i + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9db24) fc None mm (seg_rom asegs)).
  Proof.
    intros i j xt2 xa2 xt3 xt4 xt5 xt6 SX SY NZ. al_facts.
    pose proof (bx_res_cases sg sg' xs ys n i n' j SG SG' SX SY) as RC.
    pose proof SX as (I1 & I2 & I3). pose proof SY as (J1 & J2 & J3).
    pose proof b_loop3 as L3.
    pose proof SG as SG0. pose proof SG' as SG1. pose proof CX as CX1. pose proof CY as CY1. clear CX CY.
    destruct SG0 as [Es|Es]; rewrite Es in CX1; destruct SG1 as [Es'|Es']; rewrite Es' in CY1.
    all: lx_run_tac (PLAN [0x9dc88] [] 120%N); lx_tree.
    all: bx_mem; clear SG SG' PB QB.
    all: lazymatch goal with
         | |- context [MS _ _ (Z_to_bv 64 0x9dc88) _ _ _ _] =>
             assert (j = i) as -> by lia;
             bx_apply (L3 (Z.to_nat i) i RES);
             [ .. | rewrite I2, J2, Es, Es'; lia ]
         | |- _ =>
             let v := a0_of in
             assert (HV : RES = v) by lia; rewrite HV; lx_leaf
         end.
    all: first [ bx_reg | lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma b_loopY : forall (k : nat) (i j : Z) (xt1 xt3 xt4 xt5 xt6 : word),
    Z.to_nat j = k -> 0 <= j <= n' -> SIGF xs n i -> lval ys n' = lval ys j ->
    evtA asegs AL CS (POST RES)
      (MS (mkR ra SP' gp tp SHY xt1 (Z_to_bv 64 (4 * j - 4)) s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 j)
               (Z_to_bv 64 i) SB SHX (Z_to_bv 64 (4 * i - 4)) (Z_to_bv 64 (i + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9daa0) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros i j xt1 xt3 xt4 xt5 xt6 Hk Hj SX INV; al_facts.
    - (* [comment removed for export] *)
      assert (j = 0) as -> by (clear - Hk Hj; lia).
      pose proof SX as (I1 & I2 & I3).
      assert (SY : SIGF ys n' 0) by (split; [lia|]; split; [exact INV | left; reflexivity]).
      pose proof (bx_res_cases sg sg' xs ys n i n' 0 SG SG' SX SY) as RC.
      pose proof b_decide as DEC.
      lx_run_tac (PLAN [0x9daa0; 0x9db24] [] 40%N); lx_tree.
      all: bx_mem; clear SG SG' PB QB.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9db24) _ _ _ _] =>
               bx_apply (DEC i 0); [ .. | exact SX | exact SY | lia ]
           | |- _ => assert (HV : RES = 0) by lia; rewrite HV; lx_leaf
           end.
      all: first [ bx_reg | lia ].
    - assert (N1 : 1 <= j) by (clear - Hk Hj; lia).
      assert (N1y : 1 <= n') by (clear - N1 Hj; lia). pose proof (OQ N1y) as OQn.
      pose proof QB as QB'; destruct QB' as [N0|[QP QAL]]; [exfalso; clear - N0 N1y; lia|].
      pose proof b_decide as DEC.
      lx_limb HY (j - 1) wy VY.
      lx_run_tac (PLAN [0x9daa0; 0x9db24] [(0x9dae8, DJoin)] 150%N); lx_tree.
      all: bx_mem; clear SG SG' PB QB; limb_cases wy.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9daa0) _ _ _ _] =>
               assert (Z0 : limb32 ys (Z.to_nat (j - 1)) = 0) by lia;
               bx_apply (IH i (j - 1));
               [ .. | exact SX | rewrite INV; apply lval_drop_zero; [lia | exact Z0] ]
           | |- context [MS _ _ (Z_to_bv 64 0x9db24) _ _ _ _] =>
               assert (Z0 : limb32 ys (Z.to_nat (j - 1)) <> 0) by lia;
               bx_apply (DEC i j);
               [ .. | exact SX
                    | split; [lia|]; split; [exact INV | right; apply lval_top_nonzero; [lia | exact Z0]]
                    | lia ]
           end.
      all: first [ bx_reg | lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma b_loopX : forall (k : nat) (c : Z) (xt1 xt2 xa3 xa6 xt3 xt4 xt5 xt6 : word),
    Z.to_nat c = k -> 0 <= c <= n -> lval xs n = lval xs c ->
    evtA asegs AL CS (POST RES)
      (MS (mkR ra SP' gp tp (Z_to_bv 64 (4 * c - 4)) xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 c) xa3
               SB SHX xa6 (Z_to_bv 64 (-4)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9d9f0) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros c xt1 xt2 xa3 xa6 xt3 xt4 xt5 xt6 Hk Hc INV; al_facts.
    - (* [comment removed for export] *)
      assert (c = 0) as -> by (clear - Hk Hc; lia).
      pose proof b_loopY as LY0.
      lx_run_tac (PLAN [0x9d9f0; 0x9daa0] [] 60%N); lx_tree.
      all: bx_mem; clear SG SG' PB QB.
      all: bx_apply (LY0 (Z.to_nat n') 0 n');
           [ .. | reflexivity | lia | split; [lia|]; split; [exact INV | left; reflexivity] | reflexivity ].
      all: first [ bx_reg | lia ].
    - assert (N1 : 1 <= c) by (clear - Hk Hc; lia).
      assert (N1x : 1 <= n) by (clear - N1 Hc; lia). pose proof (OP N1x) as OPn.
      pose proof PB as PB'; destruct PB' as [N0|[PP PAL]]; [exfalso; clear - N0 N1x; lia|].
      pose proof b_loopY as LY0.
      lx_limb HX (c - 1) wx VX.
      lx_run_tac (PLAN [0x9d9f0; 0x9daa0] [(0x9da3c, DJoin)] 150%N); lx_tree.
      all: bx_mem; clear SG SG' PB QB; limb_cases wx.
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9d9f0) _ _ _ _] =>
               assert (Z0 : limb32 xs (Z.to_nat (c - 1)) = 0) by lia;
               bx_apply (IH (c - 1));
               [ .. | rewrite INV; apply lval_drop_zero; [lia | exact Z0] ]
           | |- context [MS _ _ (Z_to_bv 64 0x9daa0) _ _ _ _] =>
               assert (Z0 : limb32 xs (Z.to_nat (c - 1)) <> 0) by lia;
               bx_apply (LY0 (Z.to_nat n') c n');
               [ .. | reflexivity | lia
                    | split; [lia|]; split; [exact INV | right; apply lval_top_nonzero; [lia | exact Z0]]
                    | reflexivity ]
           end.
      all: first [ bx_reg | lia ].
  Qed.

  (* [comment removed for export] *)
  Lemma b_main : forall (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    abase asegs AL mm ->
    evtA asegs AL CS (POST RES)
      (MS (mkR ra SP' gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9d9ac) fc None mm (seg_rom asegs)).
  Proof.
    intros until xt6. intros AB. al_facts.
    pose proof b_loopX as LX0.
    lx_run_tac (PLAN [0x9d9f0] [] 60%N); lx_tree.
    all: bx_mem; clear SG SG' PB QB.
    all: bx_apply (LX0 (Z.to_nat n) n); [ .. | reflexivity | lia | reflexivity ].
    all: first [ bx_reg | lia ].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "00K0?K12690573793.90K8159284910.90 L12694265486.2 L13742250448.9 L13742266832.8 L1685717371.0  L19945316590.2 L20433961190.86L23515373696.2 L23515373827.2 L32049487064.81L41042576636.5 L41042593020.6 L43059266230.84L46748113268.81L57394205001.9 L57394221385.8 L8164022338.2  L9164419877.5  P23511823980.90Q15643324129.86Q25513505925.89Q45914037331.87Q49698585326.88Q58146298210.89Q67528989526.90Q9843367298.86 00000^01L01M01N01O01P01W01i01j01k02=02H02I02b03403503603703B04904N05505J05i06T07?07XS2ra2sp2dX2dY2lo3SLO2YS3PBB3QBB2HB5Ha_st5Hl_stS2ra2sp2dX2dY2lo3SLO2XS3PBB3QBB2HB5Ha_st5Hl_stFFFSS2sp2loS2sp2dX2dY3PBB3QBBFFS2sp2dX2dY3PBB3QBBS2dY2LY3QBBFS2sp2dX2dY2lo3SLO3PBB3QBBS2sp2dX2dY3PBB3QBBFFFS2dX2LX3PBBS2ra2sp2dX2dY2lo3SLO2QS2LY3PBB3QBB2HB5Ha_st5Hl_st2PS2LXS2sp2dX2dY2lo3PBB3QBBS2ra2sp2dX2dY2lo3PBB3QBB2HB5Ha_st5Hl_stS2sp2dX2dY3PBB3QBB2HBS2sp2dX2dY3SPR3PBB3QBB2HB5Ha_stS2ra2sp2dX2dY2lo3SLO3PBB3QBB2HB5Ha_st5Hl_stS2ra2sp2dX2dY2lo3SLO3PBB3QBB2HB5Ha_st5Hl_stS2sp2dX2dY2lo3SLO3PBB3QBB". (* [comment removed for export] *)
Theorem A_mpi_cmp_mpi_spec : forall AL, asan_img_ok AL -> mpi_cmp_mpi_stmtA asegs AL A_MPI_CMP_MPI_E.
Proof.
  intros AL IMG. unfold mpi_cmp_mpi_stmtA, A_MPI_CMP_MPI_E. intros until lo. intros HX HY PX PY MI ALWF CSOK AB OX OY OP OQ ST LO0 SLO SPA SCS XS YS PS QS -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  destruct (mpd_raw _ _ _ _ HX PX) as (CX & BX & LX & NX & SX & ABX & PBX).
  destruct (mpd_raw _ _ _ _ HY PY) as (CY & BY & LY & NY & SY & ABY & PBY).
  pose proof (proj1 (proj2 (proj1 HX))) as ALX. pose proof (proj1 (proj2 (proj1 HY))) as ALY.
  pose proof (proj1 (proj2 (proj2 (proj1 HX)))) as X0. pose proof (proj1 (proj2 (proj2 (proj1 HY)))) as Y0.
  pose proof (bytes_at_bound _ _ _ _ BX) as PBB. rewrite u32s_length in PBB.
  pose proof (bytes_at_bound _ _ _ _ BY) as QBB. rewrite u32s_length in QBB.
  unfold mpd_val. fold (mpd_abs dX) (mpd_abs dY). rewrite !mpd_abs_lval by assumption.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  (* [comment removed for export] *)
  zstep. zstep.
  eapply b_main; try eassumption; try reflexivity.
  all: try (clear - NX LX PBB PBX; lia).
  all: try (clear - NY LY QBB PBY; lia).
  all: try (intros N1; destruct (PS N1); [left| right]; assumption).
  all: try (intros N1; destruct (QS N1); [left| right]; assumption).
  all: try (intros N1; eapply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m);
            [unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]
            | exact MU | first [exact (OP N1) | exact (OQ N1)]]).
  all: match goal with |- ?g => idtac "CMP-TOP-LEFT:" g end.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Definition mpi_cmp_mpi_zz_stmtA (segs : list Segment) (AL : asan_layout) (ENTRY : Z) : Prop :=
  forall (CS : Z -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo X P : Z) (sw pad : word)
    (Y Q n' sg' : Z) (ys : list word) (pad' : word),
    rw_cells segs m X [C8 (Z_to_bv 64 P); C2 sw; C2 (Z_to_bv 64 0); C4 pad] ->
    X mod 8 = 0 -> 0 < X ->
    rw_cells segs m Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'] ->
    bytes_at segs m Q (u32s ys) -> Z.of_nat (length ys) = n' -> 0 <= n' <= 10000 ->
    (n' = 0 \/ 0 < Q /\ Q mod 4 = 0) -> Y mod 8 = 0 -> 0 < Y -> lval ys n' = 0 ->
    mem_inv segs m -> al_wf AL -> cs_ok AL CS -> abase segs AL m ->
    aobj segs AL CS m X 16 -> aobj segs AL CS m Y 16 -> (1 <= n' -> aobj segs AL CS m Q (4 * n')) ->
    stk segs m lo (bv_unsigned sp) -> 0 <= lo -> lo <= bv_unsigned sp - 16 -> bv_unsigned sp mod 16 = 0 ->
    crange CS lo (bv_unsigned sp - lo) ->
    (X + 16 <= lo \/ bv_unsigned sp <= X) -> (Y + 16 <= lo \/ bv_unsigned sp <= Y) ->
    (1 <= n' -> Q + 4 * n' <= lo \/ bv_unsigned sp <= Q) ->
    a0 = Z_to_bv 64 X -> a1 = Z_to_bv 64 Y ->
    evtA segs AL CS (mpi_cmp_postA segs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 ENTRY) fc None m (seg_rom segs)).

Section WalkZ.
  Variable AL : asan_layout.
  Hypothesis IMG : asan_img_ok AL.
  Hypothesis ALWF : al_wf AL.
  Local Instance lxiz : LxImg asegs AL := lxA_img AL IMG.
  Variable CS : Z -> Prop.
  Hypothesis CSOK : cs_ok AL CS.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m mm : mem) (lo : Z) (junk : list byte).
  Variables (X P : Z) (sw pad : word).
  Variables (Y Q n' sg' : Z) (ys : list word) (pad' : word).
  Hypothesis CX : rw_cells asegs mm X [C8 (Z_to_bv 64 P); C2 sw; C2 (Z_to_bv 64 0); C4 pad].
  Hypothesis XB : 0 <= X /\ X + 16 <= 2^64.
  Hypothesis CY : rw_cells asegs mm Y [C8 (Z_to_bv 64 Q); C2 (Z_to_bv 64 sg'); C2 (Z_to_bv 64 n'); C4 pad'].
  Hypothesis HY : bytes_at asegs mm Q (u32s ys).
  Hypothesis LY : Z.of_nat (length ys) = n'.
  Hypothesis Hn' : 0 <= n' <= 10000.
  Hypothesis YB : 0 <= Y /\ Y + 16 <= 2^64.
  Hypothesis QB : n' = 0 \/ 0 < Q /\ Q mod 4 = 0.
  Hypothesis YZ : lval ys n' = 0.
  Hypothesis MI : mem_inv asegs mm.
  Hypothesis ALX : X mod 8 = 0.
  Hypothesis ALY : Y mod 8 = 0.
  Hypothesis X0 : 0 < X.
  Hypothesis Y0 : 0 < Y.
  Hypothesis OX : aobj asegs AL CS mm X 16.
  Hypothesis OY : aobj asegs AL CS mm Y 16.
  Hypothesis OQ : 1 <= n' -> aobj asegs AL CS mm Q (4 * n').
  Hypothesis FR : rw_cells asegs mm (bv_unsigned sp + -16) [CB 8 junk; C8 ra].
  Hypothesis ST : stk asegs mm lo (bv_unsigned sp + -16).
  Hypothesis MU : munch [(lo, bv_unsigned sp)] m mm.
  Hypothesis WM : wmono asegs m mm.
  Hypothesis LO0 : 0 <= lo.
  Hypothesis SLO : lo <= bv_unsigned sp - 16.
  Hypothesis SCS : crange CS lo (bv_unsigned sp - lo).
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis QBB : 0 <= Q /\ Q + 4 * n' <= 2^64.

  Notation SP' := (Z_to_bv 64 (bv_unsigned sp + -16)).
  Notation SB := (Z_to_bv 64 (al_sb AL)).
  Notation SHX := (Z_to_bv 64 (Z.shiftr X 3 + al_sb AL)).
  Notation SHY := (Z_to_bv 64 (Z.shiftr Y 3 + al_sb AL)).
  Let POSTZ := mpi_cmp_postA asegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc 0 lo m.

  Ltac al_factsz :=
    pose proof (cs_ok_sb _ _ CSOK) as SB64;
    pose proof ALWF as ALWF'; unfold al_wf in ALWF';
    pose proof IMG as IMG'; unfold asan_img_ok in IMG'.
  Ltac bz_apply L :=
    first [ eapply L | eapply evtA_eq; [ apply lx_MS_regs; apply mkR_eq31 | eapply L ] ].
  Ltac bz_mem :=
    match goal with E : ?mx = mm |- _ => is_var mx; subst mx end;
    repeat match goal with
           | H : (_ =? _) = _ |- _ => clear H
           | H : (_ <? _) = _ |- _ => clear H
           | H : (if _ then _ else _) = _ |- _ => clear H
           end.
  Ltac bz_reg := lazymatch goal with |- @eq (bv _) _ _ => first [ reflexivity | f_equal; lia ] end.

  Lemma z_loopY : forall (k : nat) (j : Z) (xt1 xt3 xt4 xt5 xt6 : word),
    Z.to_nat j = k -> 0 <= j <= n' -> lval ys j = 0 ->
    evtA asegs AL CS POSTZ
      (MS (mkR ra SP' gp tp SHY xt1 (Z_to_bv 64 (4 * j - 4)) s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) (Z_to_bv 64 j)
               (Z_to_bv 64 0) SB SHX (Z_to_bv 64 (4 * 0 - 4)) (Z_to_bv 64 (0 + 1)) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
               xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9daa0) fc None mm (seg_rom asegs)).
  Proof.
    induction k as [|k IH]; intros j xt1 xt3 xt4 xt5 xt6 Hk Hj JZ; al_factsz.
    - assert (j = 0) as -> by (clear - Hk Hj; lia).
      lx_run_tac (PLAN [0x9daa0; 0x9db24] [] 40%N); lx_tree.
      all: bz_mem; lx_leaf.
    - assert (N1 : 1 <= j) by (clear - Hk Hj; lia).
      assert (N1y : 1 <= n') by (clear - N1 Hj; lia). pose proof (OQ N1y) as OQn.
      pose proof QB as QB'; destruct QB' as [N0|[QP QAL]]; [exfalso; clear - N0 N1y; lia|].
      assert (Z0 : limb32 ys (Z.to_nat (j - 1)) = 0 /\ lval ys (j - 1) = 0).
      { replace j with ((j - 1) + 1) in JZ by lia. rewrite lval_succ in JZ by lia.
        pose proof (limb32_range ys (Z.to_nat (j - 1))). pose proof (lval_range ys (j - 1) ltac:(lia)).
        pose proof (pow32_pos (j - 1) ltac:(lia)). nia. }
      destruct Z0 as [Z0 JZ'].
      lx_limb HY (j - 1) wy VY.
      lx_run_tac (PLAN [0x9daa0; 0x9db24] [(0x9dae8, DJoin)] 150%N); lx_tree.
      all: bz_mem; clear QB; destruct (bx_sw32_cases wy) as [?BW [(?&?&?)|(?&?&?)]].
      all: lazymatch goal with
           | |- context [MS _ _ (Z_to_bv 64 0x9daa0) _ _ _ _] => bz_apply (IH (j - 1)); [ .. | exact JZ' ]
           | |- _ => exfalso; lia
           end.
      all: first [ bz_reg | lia ].
  Qed.

  Lemma z_main : forall (xt0 xt1 xt2 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    abase asegs AL mm ->
    evtA asegs AL CS POSTZ
      (MS (mkR ra SP' gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 Y) xa2 xa3 xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
          F (Z_to_bv 64 0x9d9ac) fc None mm (seg_rom asegs)).
  Proof.
    intros until xt6. intros AB. al_factsz.
    pose proof z_loopY as LYZ.
    lx_run_tac (PLAN [0x9daa0] [] 80%N); lx_tree.
    all: bz_mem; clear QB.
    all: bz_apply (LYZ (Z.to_nat n') n'); [ .. | reflexivity | lia | exact YZ ].
    all: first [ bz_reg | lia ].
  Qed.

End WalkZ.

Theorem A_mpi_cmp_mpi_zz_spec : forall AL, asan_img_ok AL -> mpi_cmp_mpi_zz_stmtA asegs AL A_MPI_CMP_MPI_E.
Proof.
  intros AL IMG. unfold mpi_cmp_mpi_zz_stmtA, A_MPI_CMP_MPI_E. intros until pad'.
  intros CX ALX X0 CY BY LY NY PBY ALY Y0 YZ MI ALWF CSOK AB OX OY OQ ST LO0 SLO SPA SCS XS YS QS -> ->.
  pose proof (cs_ok_sb _ _ CSOK) as SB64. pose proof ALWF as ALWF'. unfold al_wf in ALWF'. pose proof IMG as IMG'. unfold asan_img_ok in IMG'.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn [Z.pow Z.of_N Pos.pow] in SPR.
  pose proof (rw_cells_bound _ _ _ _ CX) as ABX. pose proof (rw_cells_bound _ _ _ _ CY) as ABY. cbn [cells_size csize Nat.add] in ABX, ABY.
  pose proof (bytes_at_bound _ _ _ _ BY) as QBB. rewrite u32s_length in QBB.
  pose proof (munch_refl [(lo, bv_unsigned sp)] m) as MU. pose proof (wmono_refl asegs m) as WM.
  carve_frame 16%nat ST.
  zstep. zstep.
  eapply z_main; try eassumption; try reflexivity.
  all: try (clear - ABX; lia).
  all: try (clear - ABY; lia).
  all: try (clear - NY LY QBB PBY; lia).
  all: try (intros N1; destruct (QS N1); [left| right]; assumption).
  all: try (intros N1; eapply (aobj_munch asegs AL CS CSOK [(lo, bv_unsigned sp)] m);
            [unfold w_client; apply Forall_cons; [cbn [fst snd]; replace (lo + (bv_unsigned sp - lo)) with (bv_unsigned sp) by (clear; lia); exact SCS| apply Forall_nil]
            | exact MU | exact (OQ N1)]).
Qed.
