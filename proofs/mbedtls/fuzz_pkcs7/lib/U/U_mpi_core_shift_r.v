(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Walk MpiCoreAux CellsX.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Spec Require Import Rep.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import UImg U_string.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaOrc. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= orc_lia. (* [comment removed for export] *)
Ltac2 gd_tbl_P_mpi_core_shift_r () : Init.string Init.list := ["LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "RocqVerifyHarness.AgentSubmission.Lib.MState.MS"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.mkR"; "RocqVerifyHarness.AgentSubmission.Lib.MState.ret_pc"; "Corelib.Init.Datatypes.None"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.seg_rom"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.munch"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "MPI_CORE_SHIFT_R_STACK"; "Corelib.Init.Datatypes.nil"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.wmono"; "RocqVerifyHarness.AgentSubmission.Lib.Mem.mem_inv"; "RocqVerifyHarness.AgentSubmission.Lib.Arr.u32arr"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "Corelib.Lists.ListDef.skipn"; "Stdlib.ZArith.BinInt.Z.to_nat"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lval"; "Stdlib.ZArith.BinInt.Z.div"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.Lib.Frame.stk"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.modulo"; "Corelib.Init.Logic.or"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.Lib.Exec.evt"; "mpi_core_shift_r_post"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.limb32"; "Corelib.Init.Nat.add"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.repeat"; "RocqVerifyHarness.AgentSubmission.U.UImg.usegs"; "RocqVerifyHarness.AgentSubmission.Lib.Step.rw_cells"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.cell"; "RocqVerifyHarness.AgentSubmission.Lib.Cells.C8"; "Stdlib.Lists.List.nth_error"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.lseg"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.w32"; "RocqVerifyHarness.AgentSubmission.Lib.MpiCoreAux.same_from"].


Definition U_MPI_CORE_SHIFT_R : Z := 0x233c4.
Definition MPI_CORE_SHIFT_R_STACK : Z := 32.

Definition mpi_core_shift_r_post (segs : list Segment)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (X n cnt : Z) (xs : list word) (lo : Z) (m : mem) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Lms',$0.(1.(2.&40.)Lt0,(2.&40.)(1.(2.&40.)Lt1,(2.&40.)(1.(2.&40.)Lt2,(2.&40.)(1.(2.&40.)La0,(2.&40.)(1.(2.&40.)La1,(2.&40.)(1.(2.&40.)La2,(2.&40.)(1.(2.&40.)La3,(2.&40.)(1.(2.&40.)La4,(2.&40.)(1.(2.&40.)La5,(2.&40.)(1.(2.&40.)La6,(2.&40.)(1.(2.&40.)La7,(2.&40.)(1.(2.&40.)Lt3,(2.&40.)(1.(2.&40.)Lt4,(2.&40.)(1.(2.&40.)Lt5,(2.&40.)(1.(2.&40.)Lt6,(2.&40.)(1.P,(2.&40.)(3.(2.&8.))Lm',P,(2.&40.)(3.(2.&8.))(1.(4.(2.&40.))Lxs',(4.(2.&40.))(5.(6.$0.R12.(7.(8.O18.O17.O16.O15.R11.R10.R?.O14.O13.R>.R=.R<.R;.R:.R9.R8.R7.O12.O11.O10.O?.O>.O=.O<.O;.O:.O9.R6.R5.R4.R3.)O8.(9.O18.)O7.(:.(2.&40.))R2.(;.O19.)))(5.(<.(=.(>.$?.$?.)(10.$?.$?.O6.(11.O6.(12.+4.O5.)))(=.(>.$?.$?.)(10.$?.$?.(13.(14.&40.O17.)$15.)(14.&40.O17.))(16.(>.$?.$?.))))O1.R2.)(5.(17.O19.O1.R2.)(5.(18.O19.R2.)(5.(19.O19.R2.O6.R1.)(5.(6.$1:.(1;.(2.&40.)R1.)(1;.(2.&40.)O3.))(5.(6.(4.(2.&40.))(1<.(2.&40.)(1=.O5.)R1.)(1<.(2.&40.)(1=.O5.)O3.))(5.(6.$?.(1>.R1.O5.)(1?.(1>.O3.O5.)(20.+2.O4.)))(21.O19.R2.O2.(14.&40.O17.)))))))))))))))))))))))))))")
(* [comment removed for export] *).

Definition mpi_core_shift_r_stmt (segs : list Segment) (ENTRY : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pra,(2.&40.)Psp,(2.&40.)Pgp,(2.&40.)Ptp,(2.&40.)Pt0,(2.&40.)Pt1,(2.&40.)Pt2,(2.&40.)Ps0,(2.&40.)Ps1,(2.&40.)Pa0,(2.&40.)Pa1,(2.&40.)Pa2,(2.&40.)Pa3,(2.&40.)Pa4,(2.&40.)Pa5,(2.&40.)Pa6,(2.&40.)Pa7,(2.&40.)Ps2,(2.&40.)Ps3,(2.&40.)Ps4,(2.&40.)Ps5,(2.&40.)Ps6,(2.&40.)Ps7,(2.&40.)Ps8,(2.&40.)Ps9,(2.&40.)Ps10,(2.&40.)Ps11,(2.&40.)Pt3,(2.&40.)Pt4,(2.&40.)Pt5,(2.&40.)Pt6,(2.&40.)PF,(22.&5.(2.&40.))Pfc,(2.&20.)Pm,P,(2.&40.)(3.(2.&8.))PX,$?.Pn,$?.Pcnt,$?.Plo,$?.Pxs,(4.(2.&40.))P,(19.O2.R6.R5.R1.)P,(5.(23.+1.R5.)(23.R5.+2710.))P,(23.R6.(24.(1;.(2.&40.)R3.)))P,(5.(23.=R6.)(25.R6.(20.+2.+40.)))P,(6.$?.(26.R9.+4.)=)P,(25.=R:.)P,(21.O2.R<.R8.(14.&40.R2<.))P,(23.R9.(13.(14.&40.R2=.)$15.))P,(6.$?.(26.(14.&40.R2>.)+10.)=)P,(27.(23.(11.R>.(12.+4.(24.(1;.(2.&40.)R:.))))R;.)(23.(14.&40.R2?.)R>.))P,(18.O2.R10.)P,(6.$?.(26.(14.&40.R32.)+2.)=)P,(6.(2.&40.)R2:.(28.&40.R11.))P,(6.(2.&40.)R2:.(28.&40.R11.))P,(6.(2.&40.)R2:.(28.&40.R11.))(29.O2.(2:.O2.R36.R35.R34.R33.R2?.R2>.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R17.R16.R14.R13.R12.R10.R11.R15.)(7.(8.R36.R35.R34.R33.R32.R31.R30.R2?.R2>.R2=.R2<.R2;.R2:.R29.R28.R27.R26.R25.R24.R23.R22.R21.R20.R1?.R1>.R1=.R1<.R1;.R1:.R19.R18.)R17.(28.&40.O1.)R16.(:.(2.&40.))R15.(;.O2.)))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Local Ltac2 Set LiaOrc.tbl := fun () => "0080>L12158135620.7L12985146626.7L14736140061.7L20757219225.7L21228278198.7L28210021617.9L49721060961.9L58737526686.700000900B00N00Z00i01701E01QS2ys1n2v0S2ys1n2v0S2ys1n2v02HvS2ys1n2v02HvS2ys1n2v02Hv2HlS2ys1n2v01k2HkS2ys1n2v01k2HkS2ys1n2v02Hv". (* [comment removed for export] *)
Lemma shr_phase1_value : ltac2:(CDefT.buildp (gd_tbl_P_mpi_core_shift_r ()) "Pxs0,(4.(2.&40.))Pys,(4.(2.&40.))Pn,$?.Pv0,$?.P,(5.(23.+1.R1.)(23.R1.R2.))P,(23.R3.(24.(1;.(2.&40.)R4.)))P,Pq,$1:.P,(2;.R1.(1=.(13.R5.R4.)))(6.$?.(2<.R7.R2.)(2<.R8.(2=.R2.(1=.R5.))))(6.$?.(1>.(2>.(2.&40.)(2?.(2.&40.)(1=.(13.R5.R4.))R6.)(2>.(2.&40.)(30.(2.&40.)(28.&40.=)(1=.R4.))(1<.(2.&40.)(1=.R5.)R6.)))R5.)(1?.(1>.R7.R5.)(20.+2.(12.+20.R4.))))")
(* [comment removed for export] *).
Proof.
  intros xs0 ys n v0 Hv Hl HP.
  rewrite (lval_split _ (n - v0) n) by lia. unfold lseg.
  rewrite skipn_app, firstn_length. rewrite (skipn_all2 (firstn _ ys)) by (rewrite firstn_length; lia).
  replace (Z.to_nat (n - v0) - _)%nat with 0%nat by lia. rewrite skipn_O. cbn [app].
  rewrite lval_repeat0_app by lia. rewrite Z.mul_0_r, Z.add_0_r.
  rewrite lval_div_limbs by lia. unfold lseg.
  transitivity (lval ys (n - v0)).
  { apply lval_ext. rewrite firstn_app, firstn_firstn, firstn_length. replace (Nat.min _ _) with (Z.to_nat (n - v0)) by lia.
    replace (Z.to_nat (n - v0) - _)%nat with 0%nat by lia. cbn [firstn]. apply app_nil_r. }
  apply lval_ext_limb32. intros k Hk. rewrite HP by lia. unfold limb32. rewrite nth_skipn. f_equal. f_equal. f_equal. lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

Lemma shr_zero_value : forall (xs0 ys : list word) (n v0 : Z), 1 <= v0 <= n ->
  (forall q, (q < Z.to_nat (n - v0))%nat -> limb32 ys q = limb32 xs0 (q + Z.to_nat v0)) ->
  (forall q, (Z.to_nat (n - v0) <= q < Z.to_nat n)%nat -> limb32 ys q = 0) ->
  lval ys n = lval xs0 n / 2^(32 * v0).
Proof.
  intros xs0 ys n v0 Hv HP HZ.
  rewrite (lval_split ys (n - v0) n) by lia.
  replace (lseg ys (n - v0) n) with 0.
  2:{ symmetry. unfold lseg. apply (proj2 (lval_zero_iff (skipn (Z.to_nat (n - v0)) ys) (n - (n - v0)) ltac:(lia))). intros k Hk.
      pose proof (HZ (Z.to_nat (n - v0) + k)%nat ltac:(lia)) as H0. unfold limb32 in H0 |- *.
      rewrite nth_skipn. exact H0. }
  rewrite Z.mul_0_r, Z.add_0_r, lval_div_limbs by lia. unfold lseg.
  apply lval_ext_limb32. intros k Hk. rewrite HP by lia. unfold limb32. rewrite nth_skipn. f_equal. f_equal. f_equal. lia.
Qed.

Local Ltac zb_split K := repeat match type of K with
  | context [Z.b2z (?x <? ?y)] => revert K; destruct (Z.ltb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x <=? ?y)] => revert K; destruct (Z.leb_spec x y); cbn [Z.b2z]; intro K
  | context [Z.b2z (?x =? ?y)] => revert K; destruct (Z.eqb_spec x y); cbn [Z.b2z]; intro K
  end.
Local Ltac clear_dm := repeat match goal with
  | H : context [Z.div _ _] |- _ => clear H
  | H : context [Z.modulo _ _] |- _ => clear H
  end.
Local Ltac chk := let K := fresh "K" in if_cases K;
  [ exfalso; revert K; clear_dm; intro K; zify_cond K; rewrite ?unsigned_lit, ?signed_lit_small in K by lia;
    rewrite ?Z.shiftr_div_pow2, ?Z.shiftl_mul_pow2, ?land_3_mod' in K by lia; zb_split K;
    rewrite ?Z.lxor_0_r, ?Z.lxor_0_l, ?Z.lxor_nilpotent in K;
    lia | clear K ].
Local Ltac zeq := first [ reflexivity
  | f_equal; clear_dm; rewrite ?Z.shiftl_mul_pow2, ?zb_lxor_ones by lia; rewrite ?Z.mod_small by lia; lia
  | lazymatch goal with |- context [Z.b2z _] => idtac end; f_equal; rewrite ?land_3_mod';
    repeat match goal with |- context [Z.b2z (?x <? ?y)] => destruct (Z.ltb_spec x y) end;
    first [ reflexivity | exfalso; lia ]
  | apply Z_to_bv_eqm; clear_dm; rewrite ?Z.shiftl_mul_pow2 by lia; lia ].
Local Definition hide (P : Prop) : Prop := P.
Local Ltac unstash := repeat match goal with H : hide ?T |- _ => change T in H end.
Local Ltac stash H := let T := type of H in change (hide T) in H.
Local Ltac kfact K := revert K; clear_dm; intro K; zify_cond K; rewrite ?unsigned_lit_wrap in K; lia.

Section Walk.
  Variables (ra sp gp tp s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (s0 s1 s2 : word)
            (F : bvmap 5 word) (fc : bv 32) (m : mem)
            (X n cnt v0 v1 lx lo : Z) (xs0 : list word).
  Hypothesis Hn : 1 <= n <= 10000.
  Hypothesis Ln : n <= lx.
  Hypothesis L0 : Z.of_nat (length xs0) = lx.
  Hypothesis XB : 0 < X /\ X + 4 * lx <= 2^64.
  Hypothesis Hcnt : 0 <= cnt < 2^64.
  Hypothesis Ecnt : cnt = 32 * v0 + v1.
  Hypothesis Rv : 0 <= v0 /\ 0 <= v1 < 32.
  Hypothesis SPR : 0 <= bv_unsigned sp < 2^64.
  Hypothesis LO : lo <= bv_unsigned sp - 32.
  Hypothesis SX : X + 4 * lx <= lo \/ bv_unsigned sp <= X.
  Hypothesis RA : bv_unsigned ra mod 2 = 0.
  Hypothesis AL : X mod 4 = 0.
  Notation POST := (mpi_core_shift_r_post usegs ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc X n cnt xs0 lo m).
  Notation W := [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)].

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma tail_walk : forall (ys : list word) (mm : mem)
      (xt0 xt1 xt2 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    u32arr usegs mm X ys -> length ys = length xs0 ->
    skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 -> lval ys n = lval xs0 n / 2^cnt ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
    evt usegs POST
      (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23548) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros HX LX TX VX MU WM MI ST.
    zstep. finish. 1: exact HX. all: assumption.
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  Section WithZs.
    (* [comment removed for export] *)
    Variable zs : list word.
    Hypothesis LZ : length zs = length xs0.
    Hypothesis TZ : skipn (Z.to_nat n) zs = skipn (Z.to_nat n) xs0.
    Hypothesis VZ : lval zs n / 2^v1 = lval xs0 n / 2^cnt.

  Section Phase2.
    Hypothesis Hv1 : 0 < v1 < 32.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Lemma loop2_walk : forall (k : nat) (i : Z) (ys : list word) (r0w : word) (C R : Z) (mm : mem)
        (xt2 xt3 xt4 xt5 xt6 wt0 wt1 wa1 wa2 wa4 wa7 : word),
      Z.to_nat i = k -> 1 <= i <= n ->
      wt0 = Z_to_bv 64 (X + 4 * (i - 1)) -> wt1 = Z_to_bv 64 (X + 4 * (i - 1)) ->
      wa1 = Z_to_bv 64 (i + (2^61 - 1)) -> wa2 = Z_to_bv 64 1 -> wa4 = Z_to_bv 64 (2^64 - i) -> wa7 = Z_to_bv 64 1 ->
      u32arr usegs mm X ys -> length ys = length xs0 ->
      (forall q, (q < Z.to_nat i)%nat -> nth_error ys q = nth_error zs q) ->
      skipn (Z.to_nat n) ys = skipn (Z.to_nat n) xs0 ->
      lseg ys i n = lseg zs i n / 2^v1 ->
      lseg zs i n = C + 2^32 * R -> 0 <= C < 2^32 -> 0 <= R ->
      w32 r0w = (C mod 2^v1) * 2^(32 - v1) ->
      munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
      evt usegs POST
        (MS (mkR ra sp gp tp wt0 wt1 xt2 s0 s1 (Z_to_bv 64 X) wa1 wa2 (Z_to_bv 64 v1) wa4 r0w (Z_to_bv 64 (32 - v1)) wa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23504) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
    Proof.
      induction k as [|k IH]; intros i ys r0w C R mm xt2 xt3 xt4 xt5 xt6 wt0 wt1 wa1 wa2 wa4 wa7
        Hk Hi -> -> -> -> -> -> HX LX FY TY INV HC CB RB HR MU WM MI ST; [lia|].
      stash INV. stash HR. stash VZ.
      zstep. zstep. chk.
      zstep. zstep. chk.
      zstep. chk.
      zstep. chk.
      destruct (nth_error ys (Z.to_nat (i - 1))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
      pose proof (u32arr_read usegs mm X ys (i - 1) w _ HX NX ltac:(lia) eq_refl) as RDX.
      zstep. clear RDX.
      zstep. zstep. zstep. zstep. zstep.
      pose proof (u32arr_store_ok usegs mm X ys (i - 1) _ HX ltac:(lia) eq_refl) as SOK.
      zstep.
      lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
        pose proof (u32arr_write usegs mm X ys (i - 1) v HX ltac:(lia)) as HX';
        pose proof (limb32_upd_same ys (Z.to_nat (i - 1)) v ltac:(lia)) as VX end.
      (* [comment removed for export] *)
      assert (VW : limb32 zs (Z.to_nat (i - 1)) = w32 w).
      { apply limb32_nth_error. rewrite <- FY by lia. exact NX. }
      pose proof (w32_range w) as WR.
      rewrite (shr_limb_bits w r0w v1 (C mod 2^v1) Hv1 ltac:(apply Z.mod_pos_bound; apply Z.pow_pos_nonneg; lia) HR) in VX.
      stash VX. clear HX. store_done.
      zstep. zstep. zstep. zstep.
      if_cases Kl.
      - (* [comment removed for export] *)
        assert (Hi2 : 2 <= i) by kfact Kl. clear Kl. unstash.
        eapply (IH (i - 1) _ _ (w32 w) (lseg zs i n));
          [ lia | lia | zeq | zeq | zeq | zeq | zeq | zeq | exact HX' | rewrite upd_length; lia
          | intros q Hq; rewrite nth_error_upd_other by lia; apply FY; lia
          | rewrite skipn_upd_lt by lia; exact TY
          | | rewrite (lseg_cons zs (i - 1) n), VW by lia; f_equal; f_equal; f_equal; lia
          | lia | pose proof (lseg_range zs i n ltac:(lia)); lia
          | apply shr_carry_bits; lia
          | exact MU | exact WM | exact MI | exact ST ].
        rewrite (lseg_cons (upd ys (Z.to_nat (i - 1)) _) (i - 1) n) by lia. rewrite VX.
        replace (i - 1 + 1) with i by lia.
        replace (lseg (upd ys (Z.to_nat (i - 1)) _) i n) with (lseg ys i n)
          by (unfold lseg; rewrite skipn_upd_lt by lia; reflexivity).
        rewrite (lseg_cons zs (i - 1) n), VW by lia. replace (i - 1 + 1) with i by lia.
        eapply shr_step_arith; [lia | lia | lia | exact RB | exact HC | exact INV].
      - (* [comment removed for export] *)
        assert (Ei : i = 1) by kfact Kl. clear Kl. unstash.
        eapply tail_walk; [ exact HX' | rewrite upd_length; lia | rewrite skipn_upd_lt by lia; exact TY | | exact MU | exact WM | exact MI | exact ST ].
        rewrite <- VZ.
        assert (E0 : forall ws, lval ws n = lseg ws 0 n) by (intros; unfold lseg; cbn [Z.to_nat skipn]; f_equal; lia).
        rewrite !E0. rewrite (lseg_cons (upd ys _ _) 0 n), (lseg_cons zs 0 n) by lia.
        replace (Z.to_nat (i - 1)) with (Z.to_nat 0) in VX |- * by lia. rewrite VX.
        rewrite Ei in VW, INV, HC. replace (1 - 1) with 0 in VW by lia. rewrite VW. change (0 + 1) with 1.
        replace (lseg (upd ys (Z.to_nat 0) _) 1 n) with (lseg ys 1 n) by (unfold lseg; rewrite skipn_upd_lt by lia; reflexivity).
        eapply shr_step_arith; [lia | lia | lia | exact RB | exact HC | exact INV].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End Phase2.

    (* [comment removed for export] *)
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
    Lemma phase2_walk : forall (mm : mem) (xt0 xt1 xt2 xa2 xa4 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
      u32arr usegs mm X zs ->
      munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
      evt usegs POST
        (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) xa2 (Z_to_bv 64 v1) xa4 xa5 xa6 xa7
               s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x234c0) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
    Proof.
      intros until xt6. intros HX MU WM MI ST.
      zstep. chk.
      zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
      { (* [comment removed for export] *)
        eapply tail_walk; [exact HX | exact LZ | exact TZ | | exact MU | exact WM | exact MI | exact ST].
        rewrite <- VZ. replace v1 with 0 by lia. rewrite Z.div_1_r. reflexivity. }
      do 15 zstep.
      eapply (loop2_walk ltac:(lia) (Z.to_nat n) n zs (Z_to_bv 64 0) 0 0);
        [ reflexivity | lia | zeq | zeq | zeq | zeq | zeq | zeq | exact HX | exact LZ
        | intros; reflexivity | exact TZ
        | rewrite lseg_empty, Z.div_0_l; [reflexivity|]; apply Z.pow_nonzero; lia
        | rewrite lseg_empty; lia | lia | lia
        | rewrite Z.mod_0_l by (apply Z.pow_nonzero; lia); reflexivity
        | exact MU | exact WM | exact MI | exact ST ].
    Qed.
    Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  End WithZs.

  Lemma zero_walk : forall (k : nat) (z : Z) (ys : list word) (mm : mem)
      (xt1 xt2 xt3 xt4 xt5 xt6 wt0 wa2 wa4 wa5 wa6 wa7 : word),
    Z.to_nat (v0 - z) = k -> 0 <= z < v0 -> v0 <= n ->
    wt0 = Z_to_bv 64 (X + 4 * (n - v0 + z)) -> wa2 = Z_to_bv 64 (n - v0 + z) -> wa4 = Z_to_bv 64 (v0 - z) ->
    wa5 = Z_to_bv 64 1 -> wa6 = Z_to_bv 64 1 -> wa7 = Z_to_bv 64 (X + 4 * (n - v0 + z)) ->
    u32arr usegs mm X ys -> length ys = length xs0 ->
    (forall q, (q < Z.to_nat (n - v0))%nat -> limb32 ys q = limb32 xs0 (q + Z.to_nat v0)) ->
    (forall q, (Z.to_nat (n - v0) <= q < Z.to_nat (n - v0 + z))%nat -> limb32 ys q = 0) ->
    same_from (Z.to_nat (n - v0 + z)) ys xs0 ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
    evt usegs POST
      (MS (mkR ra sp gp tp wt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) wa2 (Z_to_bv 64 v1) wa4 wa5 wa6 wa7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23490) fc None mm (seg_rom usegs)).
  Proof.
    induction k as [|k IH]; intros z ys mm xt1 xt2 xt3 xt4 xt5 xt6 wt0 wa2 wa4 wa5 wa6 wa7
      Hk Hz Hvn -> -> -> -> -> -> HX LX HP HZ FS MU WM MI ST; [lia|].
    zstep. zstep. chk.
    zstep. zstep. chk.
    zstep. chk.
    zstep. chk.
    pose proof (u32arr_store_ok usegs mm X ys (n - v0 + z) _ HX ltac:(lia) eq_refl) as SOK.
    zstep.
    lazymatch goal with |- context [write_to_mem _ _ (le4 ?v)] =>
      pose proof (u32arr_write usegs mm X ys (n - v0 + z) v HX ltac:(lia)) as HX';
      pose proof (limb32_upd_same ys (Z.to_nat (n - v0 + z)) v ltac:(lia)) as VX end.
    assert (HP' : forall q, (q < Z.to_nat (n - v0))%nat ->
      limb32 (upd ys (Z.to_nat (n - v0 + z)) (Z_to_bv 64 0)) q = limb32 xs0 (q + Z.to_nat v0)).
    { intros q Hq. rewrite limb32_upd_other by lia. apply HP. exact Hq. }
    assert (HZ' : forall q, (Z.to_nat (n - v0) <= q < Z.to_nat (n - v0 + (z + 1)))%nat ->
      limb32 (upd ys (Z.to_nat (n - v0 + z)) (Z_to_bv 64 0)) q = 0).
    { intros q Hq. destruct (Nat.eq_dec q (Z.to_nat (n - v0 + z))) as [->|].
      - rewrite VX. reflexivity.
      - rewrite limb32_upd_other by lia. apply HZ. lia. }
    pose proof (same_from_upd _ _ _ (Z_to_bv 64 0) FS) as FS'.
    clear HX. store_done.
    zstep. zstep. zstep. zstep. zstep.
    if_cases Kl.
    - assert (Hz1 : z + 1 < v0) by kfact Kl. clear Kl.
      eapply (IH (z + 1)); [lia | lia | lia | zeq | zeq | zeq | zeq | zeq | zeq
        | exact HX' | rewrite upd_length; lia | exact HP' | exact HZ'
        | replace (Z.to_nat (n - v0 + (z + 1))) with (S (Z.to_nat (n - v0 + z))) by lia; exact FS'
        | exact MU | exact WM | exact MI | exact ST ].
    - assert (Hz1 : z + 1 = v0) by kfact Kl. clear Kl.
      eapply (phase2_walk (upd ys (Z.to_nat (n - v0 + z)) (Z_to_bv 64 0)));
        [ rewrite upd_length; lia
        | apply same_from_skipn; [| rewrite upd_length; lia];
          replace (Z.to_nat n) with (S (Z.to_nat (n - v0 + z))) by lia; exact FS'
        |
        | exact HX' | exact MU | exact WM | exact MI | exact ST ].
      rewrite (shr_zero_value xs0 _ n v0) by first [exact HP' | intros q Hq; apply HZ'; lia | lia].
      rewrite Z.div_div, <- Z.pow_add_r by (try apply Z.pow_pos_nonneg; try apply Z.pow_nonneg; lia).
      f_equal. f_equal. lia.
  Qed.

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma after_copy_walk : forall (ys : list word) (mm : mem) (xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 wa2 : word),
    1 <= v0 <= n -> wa2 = Z_to_bv 64 (n - v0) ->
    u32arr usegs mm X ys -> length ys = length xs0 ->
    (forall q, (q < Z.to_nat (n - v0))%nat -> limb32 ys q = limb32 xs0 (q + Z.to_nat v0)) ->
    same_from (Z.to_nat (n - v0)) ys xs0 ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
    evt usegs POST
      (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) wa2 (Z_to_bv 64 v1) (Z_to_bv 64 v0) xa5 xa6 xa7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x23464) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until wa2. intros Hv0 -> HX LX HP FS MU WM MI ST.
    zstep. chk.
    do 10 zstep.
    eapply (zero_walk (Z.to_nat v0) 0 ys); [lia | lia | lia | zeq | zeq | zeq | zeq | zeq | zeq
      | exact HX | exact LX | exact HP | intros; lia
      | replace (Z.to_nat (n - v0 + 0)) with (Z.to_nat (n - v0)) by lia; exact FS
      | exact MU | exact WM | exact MI | exact ST ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma loop1_walk : forall (k : nat) (j : Z) (ys : list word) (mm : mem)
      (xt5 xt6 wa2 wa5 wa6 wa7 wt0 wt1 wt2 wt3 wt4 : word),
    Z.to_nat (n - v0 - j) = k -> 0 <= j < n - v0 -> 1 <= v0 ->
    wa2 = Z_to_bv 64 (n - v0) -> wa5 = Z_to_bv 64 (4 * j) -> wa6 = Z_to_bv 64 j -> wa7 = Z_to_bv 64 1 ->
    wt0 = Z_to_bv 64 (2^64 - 1 - X) -> wt1 = Z_to_bv 64 (4 * v0) -> wt2 = Z_to_bv 64 1 ->
    wt3 = Z_to_bv 64 (X + 4 * v0 + 4 * j) -> wt4 = Z_to_bv 64 (X + 4 * j) ->
    u32arr usegs mm X ys -> length ys = length xs0 ->
    (forall q, (q < Z.to_nat j)%nat -> limb32 ys q = limb32 xs0 (q + Z.to_nat v0)) ->
    same_from (Z.to_nat j) ys xs0 ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
    evt usegs POST
      (MS (mkR ra sp gp tp wt0 wt1 wt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) wa2 (Z_to_bv 64 v1) (Z_to_bv 64 v0) wa5 wa6 wa7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 wt3 wt4 xt5 xt6) F (Z_to_bv 64 0x2341c) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    induction k as [|k IH]; intros j ys mm xt5 xt6 wa2 wa5 wa6 wa7 wt0 wt1 wt2 wt3 wt4
      Hk Hj Hv0 -> -> -> -> -> -> -> -> -> HX LX HP FS MU WM MI ST; [lia|].
    zstep. zstep. chk.
    zstep. zstep. zstep. chk.
    zstep. chk.
    zstep. chk.
    zstep. zstep. chk.
    zstep. chk.
    zstep.
    destruct (nth_error ys (Z.to_nat (j + v0))) as [w|] eqn:NX; [| apply nth_error_None in NX; lia].
    pose proof (u32arr_read usegs mm X ys (j + v0) w _ HX NX ltac:(lia) ltac:(f_equal; lia)) as RDX.
    zstep. clear RDX.
    zstep. zstep.
    pose proof (u32arr_store_ok usegs mm X ys j _ HX ltac:(lia) eq_refl) as SOK.
    zstep.
    pose proof (u32arr_write usegs mm X ys j (sx32 w) HX ltac:(lia)) as HX'.
    (* [comment removed for export] *)
    assert (VW : limb32 xs0 (Z.to_nat (j + v0)) = w32 w).
    { apply limb32_nth_error. rewrite <- (FS (Z.to_nat (j + v0))) by lia. exact NX. }
    assert (HP' : forall q, (q < S (Z.to_nat j))%nat -> limb32 (upd ys (Z.to_nat j) (sx32 w)) q = limb32 xs0 (q + Z.to_nat v0)%nat).
    { intros q Hq. destruct (Nat.eq_dec q (Z.to_nat j)) as [->|].
      - rewrite limb32_upd_same, w32_of_sx32, <- VW by lia. f_equal. lia.
      - rewrite limb32_upd_other by lia. apply HP. lia. }
    pose proof (same_from_upd _ _ _ (sx32 w) FS) as FS'.
    clear HX. store_done.
    zstep. zstep. zstep.
    if_cases Kl.
    - assert (Hj1 : j + 1 < n - v0) by kfact Kl. clear Kl.
      eapply (IH (j + 1)); [lia | lia | lia | zeq | zeq | zeq | zeq | zeq | zeq | zeq | zeq | zeq
        | exact HX' | rewrite upd_length; lia
        | replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; exact HP'
        | replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia; exact FS'
        | exact MU | exact WM | exact MI | exact ST ].
    - assert (Hj1 : j + 1 = n - v0) by kfact Kl. clear Kl.
      eapply (after_copy_walk (upd ys (Z.to_nat j) (sx32 w))); [lia | zeq | exact HX' | rewrite upd_length; lia
        | replace (Z.to_nat (n - v0)) with (S (Z.to_nat j)) by lia; exact HP'
        | replace (Z.to_nat (n - v0)) with (S (Z.to_nat j)) by lia; exact FS'
        | exact MU | exact WM | exact MI | exact ST ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)

  (* [comment removed for export] *)
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
  Lemma phase1_walk : forall (mm : mem) (xt0 xt1 xt2 xa5 xa6 xa7 xt3 xt4 xt5 xt6 : word),
    v0 <= n -> v0 < n \/ v1 = 0 ->
    u32arr usegs mm X xs0 ->
    munch W m mm -> wmono usegs m mm -> mem_inv usegs mm -> stk usegs mm lo (bv_unsigned sp) ->
    evt usegs POST
      (MS (mkR ra sp gp tp xt0 xt1 xt2 s0 s1 (Z_to_bv 64 X) (Z_to_bv 64 n) (Z_to_bv 64 cnt) (Z_to_bv 64 v1) (Z_to_bv 64 v0) xa5 xa6 xa7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6) F (Z_to_bv 64 0x233e4) fc None mm (seg_rom usegs))
(* [comment removed for export] *).
  Proof.
    intros until xt6. intros Hv0 Hdis HX MU WM MI ST.
    zstep. zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
    { (* [comment removed for export] *)
      eapply (phase2_walk xs0); [reflexivity | reflexivity | | exact HX | exact MU | exact WM | exact MI | exact ST ].
      f_equal. f_equal. lia. }
    assert (Hv0' : 1 <= v0) by lia.
    zstep. zstep. if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia.
    { (* [comment removed for export] *)
      eapply (after_copy_walk xs0); [lia | zeq | exact HX | reflexivity | intros; lia | apply same_from_refl
        | exact MU | exact WM | exact MI | exact ST ]. }
    do 10 zstep.
    eapply (loop1_walk (Z.to_nat (n - v0)) 0 xs0); [lia | lia | lia | zeq | zeq | zeq | zeq | zeq | zeq | zeq | zeq | zeq
      | exact HX | reflexivity | intros; lia | apply same_from_refl | exact MU | exact WM | exact MI | exact ST ].
  Qed.
  Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
End Walk.

Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
Lemma U_mpi_core_shift_r_spec : mpi_core_shift_r_stmt usegs U_MPI_CORE_SHIFT_R.
Proof.
  unfold mpi_core_shift_r_stmt, U_MPI_CORE_SHIFT_R.
  intros until xs. intros HX Hn LX Hcnt ALX NZX ST LO SPA SX MI RA -> -> ->.
  unfold MPI_CORE_SHIFT_R_STACK in *.
  pose proof (munch_refl [(X, X + 4 * n); (bv_unsigned sp - 32, bv_unsigned sp)] m) as MU.
  pose proof (wmono_refl usegs m) as WM.
  pose proof (u32arr_bound _ _ _ _ HX) as XB.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  pose proof (Z.div_mod cnt 32 ltac:(lia)) as DM. pose proof (Z.mod_pos_bound cnt 32 ltac:(lia)) as MB.
  zstep. rewrite Z.shiftr_div_pow2 by lia. change (2^5) with 32.
  zstep. if_cases K1; zify_cond K1; rewrite ?unsigned_lit in K1 by lia.
  2: zstep; rewrite land_31_mod; zstep; if_cases K2; zify_cond K2; rewrite ?unsigned_lit in K2 by lia;
     [| zstep; if_cases K3; zify_cond K3; rewrite ?unsigned_lit in K3 by lia].
  (* [comment removed for export] *)
  2,3: eapply (@phase1_walk) with (v0 := cnt / 32) (v1 := cnt mod 32); try eassumption; try reflexivity; try lia.
  (* [comment removed for export] *)
  all: zstep; zstep; zstep.
  all: rewrite !Z.shiftl_mul_pow2 by lia; change (2^2) with 4.
  all: pose proof (firstn_skipn (Z.to_nat n) xs) as EY; symmetry in EY;
       assert (LB : length (firstn (Z.to_nat n) xs) = Z.to_nat n) by (rewrite firstn_length; lia).
  all: rewrite EY in HX; apply u32arr_app in HX; destruct HX as [HXB HXC]; rewrite LB in HXC;
       apply u32arr_cells in HXB; rewrite LB in HXB.
  all: pose proof U_memset_spec as SP; unfold memset_stmt in SP.
  all: eapply evt_cut; [ eapply SP; [|exact MI]; rewrite !unsigned_lit by lia;
                         replace (Z.to_nat (n * 4)) with (4 * Z.to_nat n)%nat by lia; exact HXB | ].
  all: clear SP HXB; unfold memset_post; rewrite !unsigned_lit by lia.
  all: match goal with H : mem_inv usegs ?mc |- _ => post_call usegs mc end.
  all: match goal with H : rw_cells usegs ?m2 ?X' [CB _ (repeat _ _)] |- _ =>
      constr_eq X' X;
      apply (u32arr_of_cells usegs m2 _ _ _ (repeat (Z_to_bv 64 0) (Z.to_nat n))) in H;
      [| rewrite u32s_repeat0; replace (bv_unsigned (Z_to_bv 64 0) mod 256) with 0 by reflexivity; f_equal; lia ];
      rename H into HXB
    end.
  all: lazymatch type of HXB with u32arr _ ?m2 _ _ =>
       assert (HX' : u32arr usegs m2 X (repeat (Z_to_bv 64 0) (Z.to_nat n) ++ skipn (Z.to_nat n) xs))
       by (apply u32arr_app; split; [exact HXB|]; rewrite repeat_length; replace (4 * Z.of_nat (Z.to_nat n)) with (4 * Z.of_nat (Z.to_nat n)) by lia;
           lazymatch type of HXC with u32arr _ _ ?a _ => replace (X + 4 * Z.of_nat (Z.to_nat n)) with a by lia end; exact HXC) end.
  all: finish.
  all: try exact HX'.
  all: try (rewrite app_length, repeat_length, skipn_length; lia).
  all: try (rewrite skipn_app, repeat_length, skipn_all2 by (rewrite repeat_length; lia); rewrite Nat.sub_diag; reflexivity).
  all: rewrite lval_repeat0_app by lia; symmetry; apply Z.div_small; split; [apply (proj1 (lval_range xs n ltac:(lia)))|];
       eapply Z.lt_le_trans; [apply (proj2 (lval_range xs n ltac:(lia)))|]; apply Z.pow_le_mono_r; lia.
Qed.
Local Ltac2 Set LiaOrc.tbl := fun () => "". (* [comment removed for export] *)
