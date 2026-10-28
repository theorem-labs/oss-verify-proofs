(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux MpiWalkAux.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LXP Require Import LxPMpiTac.
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Import OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.LxhSyntax. #[local] Instance lxh_tab : OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lx_hints := OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LX.LxDec.lxh_parse "P02491e347f267c57 0 2 0 1 51 1P03debae7b424ff99 1 1 4 3 0 1 16 1 42 1 2 12 1 53 1P03e510e797015c1f 2 48 1 1 4 6 0 1 2 1 13 4 25 4 43 1 46 1 2 26 1 53 1 1 1 4 6 0 1 1 1 14 4 25 4 44 1 45 1 2 26 1 53 1P05c8526a672311ab 0 2 0 1 5 1P0c6666dc69097d49 0 2 0 1 5 1P0cc47c23329752ae 0 2 0 1 10 1P0e17cf254bfb142f 0 3 0 4294967296 7 4294967296 27 1P11270532eaf521d2 0 2 0 1 10 1P12dee023fc8fda76 0 4 0 1 14 4 15 1 41 1P13d4afe7f9bc9775 0 2 0 1 4 1P147f8b2cba13c595 0 3 0 1 52 1 54 1P14b4cedf5ff83c4a 0 2 0 1 4 1P16a6c9ec19ec1fcb 0 2 0 1 51 1P1f738e974621c56d 0 4 0 1 25 4 42 1 45 1P21436a93afaa9540 0 2 0 1 6 4294967296P22726b974061a676 0 2 0 1 51 1P2366e7fbd0478460 0 2 0 1 10 1P2375f0be35b18fc7 0 2 0 1 5 1P23c8d9107829256c 0 3 0 1 51 1 53 1P2465e6eb89bc139e 0 4 0 1 25 4 42 1 45 1P293f3480baf0c9c0 2 48 1 1 16 6 0 4 3 4 34 16 47 4 54 4 55 4 2 27 1 56 1 0 7 0 1 2 1 15 4 26 4 46 1 54 1 55 1P2ea669cacf0fef86 0 2 0 1 51 1P32d0c8d9f8fc1775 1 1 4294967296 1 0 1 2 7 1 26 1P33fea5ea4fe0261e 1 1 4294967296 1 28 1 3 0 1 8 1 29 1P34c18deec13839ec 0 2 0 1 9 1P38596ab93c5fc0f2 0 3 0 1 26 1 51 1P3c8e54fd6a777515 0 2 0 1 51 1P3fc622bf3fada53e 0 2 0 1 51 1N011607f5a453ad84N020a8afa92e68857N032bfc23a8ec56ceN040f900fbc3bb74aN058f134221d9eeb5N0783ada30209ec98N09395e3c06cc70c6N0b242090626d0fc9N0cf313fe06f3420bN0d3064abaa8282d8N0f6bda0759fb0052N0fa85f2a8a1a1182N11890c9d0c01c881N12a4ed83286f1870N12b58f69d468dcc9N168d03ba2bac0cc0N16baaf53496253b3N16e784c46a7cdfc2N17f9571eea3eaaa5N1a3a40e2e3d6fdceN1b6ef83157bfb09bN1deeaec24b989c26N1ead44715a5595a4N1f3de557c3a57f28N1fceff8844d183d6N24c151c1be96b730N253ad1500b35dfceN26daed07a8c92a5aN27c93671606e9659N281fc8e4c5c81489N2a1014ff3d513910N2a83ad31c35d1f31N2c0329e287cb1027N3014e6fc3ec6ce83N3126cf36d4a40999N32251f22b4f8e9c6N34b35daaeade61d2N34e1ba74991b1ff2N35e89d4b2bb85e71N364da718bb3a4584N38962268e529fea3N38cbf1ef84a41797N39c31e35318e1e1cN3a0dbdb7971a7fbfN3bd8bfacf09e62e0N3c4e3b6233a5484bN3c5e0c783eb172dcN3e4a0d65de657f97N3f40bdc3ef88ffde"%lxh.
Ltac2 gd_tbl_P_mpi_core_add_if () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Datatypes.option"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.list"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.bytes_at"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32s"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Corelib.Init.Logic.eq"; "Stdlib.ZArith.BinInt.Z.modulo"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.sub"; "MPI_CORE_ADD_IF_STACK"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_add_if_post"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "Stdlib.ZArith.BinInt.Z.shiftr"; "stdpp.bitvector.definitions.bv_signed"; "Stdlib.ZArith.BinInt.Z.lor"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.ct_mask"].


Definition U_MPI_CORE_ADD_IF : Z := 0x237b0.
Definition MPI_CORE_ADD_IF_STACK : Z := 16.

Definition mpi_core_add_if_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n cond : Z) (xs ys : list word) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (c : Z) (xs' : list word),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom segs)
    /\ munch [(X, X + 4 * n); (bv_unsigned sp - MPI_CORE_ADD_IF_STACK, bv_unsigned sp)] m m'
    /\ wmono segs m m' /\ mem_inv segs m'
    /\ a0 = Z_to_bv 64 c /\ 0 <= c <= 1
    /\ u32arr segs m' X xs' /\ length xs' = length xs
    /\ skipn (Z.to_nat n) xs' = skipn (Z.to_nat n) xs
    /\ lval xs' n + c * 2^(32 * n) = lval xs n + (if cond =? 0 then 0 else lval ys n)
    /\ stk segs m' lo (bv_unsigned sp).

Definition mpi_core_add_if_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_add_if ()) "Pra,(0.&40.)Psp,(0.&40.)Pgp,(0.&40.)Ptp,(0.&40.)Pt0,(0.&40.)Pt1,(0.&40.)Pt2,(0.&40.)Ps0,(0.&40.)Ps1,(0.&40.)Pa0,(0.&40.)Pa1,(0.&40.)Pa2,(0.&40.)Pa3,(0.&40.)Pa4,(0.&40.)Pa5,(0.&40.)Pa6,(0.&40.)Pa7,(0.&40.)Ps2,(0.&40.)Ps3,(0.&40.)Ps4,(0.&40.)Ps5,(0.&40.)Ps6,(0.&40.)Ps7,(0.&40.)Ps8,(0.&40.)Ps9,(0.&40.)Ps10,(0.&40.)Ps11,(0.&40.)Pt3,(0.&40.)Pt4,(0.&40.)Pt5,(0.&40.)Pt6,(0.&40.)PF,(1.&5.(0.&40.))Pfc,(0.&20.)Pm,P,(0.&40.)(2.(0.&8.))PX,$3.PA,$3.Pn,$3.Pcond,$3.Plo,$3.Pxs,(4.(0.&40.))Pys,(4.(0.&40.))P,(5.O2.R8.R7.R2.)P,(6.O2.R9.R7.(7.R2.))P,(8.(9.=R7.)(9.R7.+2710.))P,(9.R8.(:.(;.(0.&40.)R5.)))P,(9.R9.(:.(;.(0.&40.)R5.)))P,(8.(9.=R9.)(<.R9.(=.+2.+20.)))P,(>.(9.(?.R<.(10.+4.(:.(;.(0.&40.)R7.))))R=.)(9.(?.R=.(10.+4.(:.(;.(0.&40.)R8.))))R<.))P,(11.$3.(12.R>.+4.)=)P,(11.$3.(12.R>.+4.)=)P,(<.=R10.)P,(<.=R10.)P,(13.O2.R13.R>.(14.&40.R33.))P,(9.R?.(15.(14.&40.R34.)$16.))P,(11.$3.(12.(14.&40.R35.)+10.)=)P,(>.(9.(?.R15.(10.+4.(:.(;.(0.&40.)R10.))))R11.)(9.(14.&40.R36.)R15.))P,(>.(9.(?.R15.(10.+4.(:.(;.(0.&40.)R10.))))R12.)(9.(14.&40.R37.)R15.))P,(17.O2.R18.)P,(11.(0.&40.)R31.(18.&40.R18.))P,(11.(0.&40.)R31.(18.&40.R18.))P,(11.(0.&40.)R31.(18.&40.R18.))P,(11.(0.&40.)R31.(18.&40.R18.))(19.O2.(1:.O2.R3>.R3=.R3<.R3;.R37.R36.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R1?.R1>.R1<.R1:.R19.R17.R16.R18.R1=.)(1;.(1<.R3>.R3=.R3<.R3;.R3:.R39.R38.R37.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.)R1?.(18.&40.O1.)R1>.(1=.(0.&40.))R1=.(1>.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Lemma ct_bool_mask : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_add_if ()) "Pcond,$3.P,(8.(9.=R1.)(<.R1.(=.+2.+20.)))(11.(0.&40.)(18.&40.(1?.(20.&40.(18.&40.(21.(12.(15.=(1?.(12.R2.+100000000.)+1.))+10000000000000000.)(12.(15.=(12.R2.+100000000.))+10000000000000000.))))+3?.))(18.&40.(22.R2.)))")
(* [comment removed for export] *).
Proof.
  intros cond Hc. unfold ct_mask. destruct (Z.eqb_spec cond 0) as [->|NE].
  - vm_compute. reflexivity.
  - rewrite (Z.mod_small cond 4294967296) by lia.
    set (a := (0 - Z.shiftr cond 1) mod 18446744073709551616). set (b := (0 - cond) mod 18446744073709551616).
    assert (Hb : 2^63 <= b < 2^64).
    { subst b. rewrite <- (Z.mod_add _ 1) by lia. rewrite Z.mod_small by lia. lia. }
    assert (Ha : 0 <= a < 2^64) by (subst a; apply Z.mod_pos_bound; lia).
    assert (HL : 2^63 <= Z.lor a b < 2^64).
    { pose proof (lor_ge_r a b ltac:(lia) ltac:(lia)). pose proof (lor_lt_pow2 a b 64 ltac:(lia) ltac:(lia)). lia. }
    rewrite zb_signed, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
    rewrite Z.mod_small by lia.
    destruct (Z.ltb_spec (Z.lor a b) (2^63)); [lia|].
    rewrite Z.shiftr_div_pow2 by lia.
    replace ((Z.lor a b - 2^64) / 2^63) with (-1) by (apply Z.div_unique with (r := Z.lor a b - 2^63); lia).
    apply Z_to_bv_eqm. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma ct_select0 : forall (w : word) cond,
  Z.land (bv_unsigned (sx32 w)) (ct_mask cond) = bv_unsigned (sx32 (if cond =? 0 then Z_to_bv 64 0 else w)).
Proof.
  intros w cond. unfold ct_mask. destruct (cond =? 0).
  - rewrite Z.land_0_r. vm_compute. reflexivity.
  - replace (2^64 - 1) with (Z.ones 64) by reflexivity. pose proof (bv_unsigned_in_range 64 (sx32 w)) as R. unfold bv_modulus in R.
    rewrite Z.land_ones by lia. apply Z.mod_small. exact R.
Qed.

Lemma w32_select0 : forall (w : word) cond, w32 (if cond =? 0 then Z_to_bv 64 0 else w) = (if cond =? 0 then 0 else w32 w).
Proof. intros w cond. destruct (cond =? 0); [vm_compute|]; reflexivity. Qed.

Definition addif_inv (xs : list word) (i c : Z) (xs0 ys0 : list word) (cond : Z) : Prop :=
  lval xs i + c * 2^(32 * i) = lval xs0 i + (if cond =? 0 then 0 else lval ys0 i).

Lemma addif_inv_0 : forall xs xs0 ys0 cond, addif_inv xs 0 0 xs0 ys0 cond.
Proof. intros. unfold addif_inv. rewrite !lval_0. destruct (cond =? 0); lia. Qed.

Lemma addif_inv_step : forall xs xs' xs0 ys0 cond i c c', 0 <= i -> addif_inv xs i c xs0 ys0 cond -> lval xs' i = lval xs i ->
  limb32 xs' (Z.to_nat i) + 2^32 * c' = limb32 xs0 (Z.to_nat i) + (if cond =? 0 then 0 else limb32 ys0 (Z.to_nat i)) + c ->
  addif_inv xs' (i + 1) c' xs0 ys0 cond.
Proof.
  intros xs xs' xs0 ys0 cond i c c' Hi INV EQ ST. unfold addif_inv in *.
  rewrite !lval_succ, pow2_32_succ, EQ by lia. set (M := 2 ^ (32 * i)) in *.
  destruct (cond =? 0); nia.
Qed.


Lemma addif_inv_next : forall (l l0 ly : list word) (i c c' cnd : Z) (wx wa v : word),
  addif_inv l i c l0 ly cnd -> 0 <= i -> (Z.to_nat i < length l)%nat ->
  limb32 l0 (Z.to_nat i) = w32 wx -> limb32 ly (Z.to_nat i) = w32 wa ->
  w32 v + 2 ^ 32 * c' = w32 wx + (if cnd =? 0 then 0 else w32 wa) + c ->
  addif_inv (upd l (Z.to_nat i) v) (i + 1) c' l0 ly cnd.
Proof.
  intros l l0 ly i c c' cnd wx wa v INV Hi HL VX VA V.
  eapply addif_inv_step; [exact Hi | exact INV | apply lval_upd_ge; lia | rewrite (limb32_upd_same _ _ _ HL), VX, VA; exact V].
Qed.

Section Walk.
  Variables (ra sp gp tp t0 t1 t2 a7_dummy s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X A n cond lx la lo : Z) (xs0 ys0 : list word).
  Hypothesis Hn : 0 <= n <= 10000.
  Hypothesis Ln : n <= lx /\ n <= la.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis LA : Z.of_nat (length ys0) = la.
  Hypothesis DA : A + 4 * la <= X \/ X + 4 * lx <= A.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis AB : 0 < A /\ A + 4 * la <= 2^64.
  Hypothesis ALX : X mod 4 = 0.
  Hypothesis ALA : A mod 4 = 0.
  Hypothesis HC : 0 <= cond < 2^32.
  Hypothesis LO : 0 <= lo <= bv_unsigned sp - 16.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis SA : A + 4 * la <= lo \/ bv_unsigned sp <= A.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.

  Notation POST := (mpi_core_add_if_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cond xs0 ys0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 16, bv_unsigned sp)].

  (* [comment removed for export] *)
  Lemma loop_walk : forall (k : nat) (i c : Z) (xs ys : list word) (x8 x31 : word) mm (j : list byte) (ex ea mk : Z),
    Z.to_nat (n - i) = k -> 0 <= i < n -> 0 <= c <= 1 ->
    ex = X + 4 * i -> ea = A + 4 * i -> mk = (if cond =? 0 then 0 else -1) ->
    u32arr usegs mm X xs -> Z.of_nat (length xs) = lx -> same_from (Z.to_nat i) xs xs0 ->
    addif_inv xs i c xs0 ys0 cond ->
    bytes_at usegs mm A (u32s ys) -> Z.of_nat (length ys) = la -> same_from (Z.to_nat i) ys ys0 ->
    stk usegs mm lo (bv_unsigned sp + -16) -> length j = 8%nat ->
    rw_cells usegs mm (bv_unsigned sp + -16) [C8 (le_bytes_to_word j); C8 s0] ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm ->
    evt usegs POST
      (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -16)) gp tp (Z_to_bv 64 mk) (Z_to_bv 64 1) (Z_to_bv 64 ex) x8 s1
              (Z_to_bv 64 X) (Z_to_bv 64 A) (Z_to_bv 64 n) (Z_to_bv 64 c) (Z_to_bv 64 i)
              (Z_to_bv 64 1) (Z_to_bv 64 1) (Z_to_bv 64 1) s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
              (Z_to_bv 64 ea) (Z_to_bv 64 ea) (Z_to_bv 64 ex) x31)
          F (Z_to_bv 64 0x23810) fc None mm (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros i c xs ys x8 x31 mm j ex ea mk Hk Hi Hc Ex Ea Emk HX LX FX INV HA LA' FA ST LXJ FR MU WM MI;
      [exfalso; xlia Hk Hi|].
    lx_limb_ro HA FA i Ea (proj1 Hi) ltac:(xlia Hi LA' Ln) wa VA.
    lx_limb_rw HX i Ex (proj1 Hi) ltac:(xlia Hi LX Ln) wx NX.
    pose proof (same_from_limb32 _ _ _ _ _ FX (PeanoNat.Nat.le_refl _) NX) as VX0.
    lx_hide MU. lx_hide WM. lx_hide HX.
    pose proof (munch_refl ([] : list ivl) mm) as MUl0. pose proof (wmono_refl usegs mm) as WMl0.
    lx_run_tac (PLAN [0x23810] [] 80%N); lx_tree.
    all: lx_unhide; lx_gc; try clear MUl0; try clear WMl0.
    (* [comment removed for export] *)
    all: first [ lazymatch goal with DEF : ?cv = Z.b2z _ + Z.b2z _ |- _ =>
           first [ destruct (lx_core_addif_exact wx wa c cv mk cond Hc Emk DEF) as [Hc' V]
                 | rewrite Z.add_comm in DEF; destruct (lx_core_addif_exact wx wa c cv mk cond Hc Emk DEF) as [Hc' V] ]; clear DEF end
         | lazymatch goal with |- context [MS (mkR _ _ _ _ _ _ _ _ _ _ _ _ (Z_to_bv 64 ?cv) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _] =>
           first [ destruct (lx_core_addif_exact wx wa c cv mk cond Hc Emk eq_refl) as [Hc' V]
                 | destruct (lx_core_addif_exact wx wa c cv mk cond Hc Emk (Z.add_comm _ _)) as [Hc' V] ] end ].
    all: lx_rn_rw ex CX'; lx_rn_munch MUl; lx_rn_wmono WMl; lx_rn_mi MI'; lx_rn_stk ST'; lx_rn_ro32 A HA'.
    all: try lx_rn_rw (bv_unsigned sp + -16) FR'.
    all: pose proof (u32arr_upd_of_cell _ _ _ _ _ _ _ _ HX NX (proj1 Hi) Ex MUl WMl CX') as HX';
         pose proof (munch_local1 _ _ _ _ _ _ _ _ _ eq_refl MU MUl ltac:(xlia Ex Hi) ltac:(xlia Ex Hi)) as MU';
         pose proof (wmono_trans _ _ _ _ WM WMl) as WM'.
    all: lazymatch goal with
    | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23810) _ _ _ _) =>
      (* [comment removed for export] *)
      eapply (IH (i + 1)); [xlia Hk Hi | klia | exact Hc' | xlia Ex | xlia Ea | exact Emk
        | exact HX' | exact (upd_length_Z _ _ _ _ LX) | exact (same_from_upd_Z _ _ _ _ FX (proj1 Hi))
        | exact (addif_inv_next _ _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VX0 VA V)
        | exact HA' | exact LA' | eapply same_from_weaken; [exact FA | xlia Hi]
        | exact ST' | exact LXJ | first [exact FR' | eassumption] | exact MU' | exact WM' | exact MI' ]
    | |- _ =>
      (* [comment removed for export] *)
      lx_post;
      lazymatch goal with
           | |- munch _ _ _ => exact MU'
           | |- wmono _ _ _ => exact WM'
           | |- u32arr _ _ _ _ => exact HX'
           | |- @eq nat (length _) _ => rewrite upd_length; xlia LX L0
           | |- skipn _ _ = skipn _ _ => eapply skipn_upd_Z; [exact FX | xlia Hi | klia | xlia LX L0]
           | |- lval _ ?nn + _ = _ => replace nn with (i + 1) by klia; exact (addif_inv_next _ _ _ _ _ _ _ _ _ _ INV (proj1 Hi) ltac:(xlia Hi LX Ln) VX0 VA V)
           | |- _ => first [reflexivity | assumption | xlia Hc']
           end
    end.
    all: match goal with |- ?g => idtac "LOOP-LEFT:" g end.
  Qed.
End Walk.

Lemma U_mpi_core_add_if_spec : mpi_core_add_if_stmt usegs U_MPI_CORE_ADD_IF.
Proof.
  unfold mpi_core_add_if_stmt, U_MPI_CORE_ADD_IF.
  intros until ys. intros HX HA Hn LX LA HC DA ALX ALA NZX NZA ST LO SPA SX SA MI -> -> -> ->.
  unfold MPI_CORE_ADD_IF_STACK in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 16, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB. pose proof (u32ro_bound _ _ _ _ HA) as AB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  (* [comment removed for export] *)
  carve_frame 16%nat ST; lxp_split_frame [8;8]%nat.
  lx_run_tac (PLAN [0x23810] [] 40%N); lx_tree.
  all: lx_gc; try lx_same_mem.
  all: lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 0x23810) _ _ _ _) =>
    eapply (@loop_walk) with (X := X) (A := A) (n := n) (cond := cond) (lo := lo)
             (lx := Z.of_nat (length xs)) (la := Z.of_nat (length ys)) (xs0 := xs) (ys0 := ys)
             (k := Z.to_nat (n - 0)) (i := 0) (c := 0) (xs := xs) (ys := ys) (j := j);
    try assumption;
    lazymatch goal with
         | |- Z.shiftr _ 63 = _ => exact (lx_ct_mask_sra _ HC)
         | |- same_from _ _ _ => apply same_from_refl
         | |- addif_inv _ _ _ _ _ _ => apply addif_inv_0
         | |- 0 <= 0 < _ => klia
         | |- _ /\ _ => first [xlia LX LA | xlia XB NZX | xlia AB NZA | xlia LO0 LO | xlia0 | klia]
         | |- munch _ _ _ => first [eassumption | exact MU | apply munch_refl]
         | |- wmono _ _ _ => first [eassumption | exact WM | apply wmono_refl]
         | |- _ => first [ eassumption | reflexivity | xlia0 | klia ]
         end
  | |- _ =>
    (* [comment removed for export] *)
    (let xn := constr:(n) in match goal with K : 0 <= - xn |- _ => rename K into BR | _ => idtac end);
    lx_post; first [reflexivity | eassumption | apply munch_refl | apply wmono_refl | xlia Hn BR
                   | rewrite !lval_nonpos by xlia Hn BR; lazymatch goal with |- context [if ?cn =? 0 then _ else _] => destruct (cn =? 0); xlia0 end | idtac]
  end.
  all: match goal with |- ?g => idtac "LEFT:" g end.
Qed.
