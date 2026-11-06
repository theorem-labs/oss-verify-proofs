(* This file states or restates instruction words of the task's compiled program (third-party object code: the upstream library at its pinned commit, the C library, the sanitizer runtime and the task authors' wrapper) for use in the proofs - see NOTICE. No Anthropic licence header is applied to this file. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac tauto ::= OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac.wd_tauto.   (* [comment removed for export] *)
Module AsAllocM2s.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= hs_am_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section AMS.
  Variable segs : list Segment.
  Variable t : am_tab.
  Hypothesis TOK : am_tab_ok segs t.
  #[local] Abbreviation rb := (am_rb t).
  #[local] Abbreviation INST := (am_inst t).

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp stk : word) (n : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = Z_to_bv 64 n.
  Hypothesis H11 : getr regs 11 = stk.
  Hypothesis Hs : (64513 <= n <= 2 ^ 34)%Z.
  (* [comment removed for export] *)
  Variable MAG : word.
  Hypothesis Rinited : rdn segs mem (Z_to_bv 64 (am_g_inited t)) 1 = Some [Z_to_bv 8 1].
  Hypothesis Rrss : rdn segs mem (Z_to_bv 64 (am_g_rss t)) 1 = Some [Z_to_bv 8 0].
  Hypothesis Rmag : rdn segs mem (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw).
  Hypothesis Rtbl2 : rdn segs mem (at_ (am_tbl2 t) 4) 1 = Some [Z_to_bv 8 3].     (* [comment removed for export] *)
  Hypothesis Rt16 : rdn segs mem (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis Rt2048 : rdn segs mem (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis Rminrz : rdn segs mem (at_ INST 3624) 2 = Some (LE2 16).
  Hypothesis Rmaxrz : rdn segs mem (at_ INST 3626) 2 = Some (LE2 2048).
  Hypothesis Rmaxsz : rdn segs mem (at_ INST 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  Hypothesis Hstk : store_ok segs mem (at_ sp (-160)) 160 = true.
  (* [comment removed for export] *)
  Hypothesis G0 : (0 <= am_g_inited t < 2 ^ 32)%Z /\ (0 <= am_g_rss t < 2 ^ 32)%Z /\ (0 <= am_g_magic t /\ am_g_magic t + 8 <= 2 ^ 32)%Z
            /\ (U (am_tbl2 t) + 64 <= 2 ^ 32)%Z /\ (U (am_tbl t) + 64 <= 2 ^ 32)%Z /\ (U INST + 4096 <= 2 ^ 32)%Z /\ (U stk <> 0)%Z.
  Hypothesis G1 : (2 ^ 32 + 160 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r am_clobx).

  #[local] Abbreviation am_m1 := (AsAllocM2.am_m1 t regs mem ra sp).
  #[local] Abbreviation am_m2 := (AsAllocM2.am_m2 t regs mem ra sp).
  #[local] Abbreviation am_m3 := (AsAllocM2.am_m3 t regs mem ra sp).
  #[local] Hint Unfold AsAllocM2.am_m1 AsAllocM2.am_m2 AsAllocM2.am_m3 : asfr.
  Let RETa := AsAllocM2.RETa segs t TOK.
  Let am_m1_outside := AsAllocM2.am_m1_outside t regs mem ra sp G1.
  Let am_m2_outside := AsAllocM2.am_m2_outside t regs mem ra sp G1.
  Let am_m3_outside := AsAllocM2.am_m3_outside t regs mem ra sp G1.
  Let I66af0 := AsAllocM2.I66af0 segs t TOK.
  Let I66b58 := AsAllocM2.I66b58 segs t TOK.
  Let I66b5c := AsAllocM2.I66b5c segs t TOK.
  Let I66b68 := AsAllocM2.I66b68 segs t TOK.
  Let I66b6c := AsAllocM2.I66b6c segs t TOK.
  Let I66b78 := AsAllocM2.I66b78 segs t TOK.
  Let I66b7c := AsAllocM2.I66b7c segs t TOK.
  Let I66b80 := AsAllocM2.I66b80 segs t TOK.
  Let I66b8c := AsAllocM2.I66b8c segs t TOK.
  Let I66b90 := AsAllocM2.I66b90 segs t TOK.
  Let I66b94 := AsAllocM2.I66b94 segs t TOK.
  Let I66ba0 := AsAllocM2.I66ba0 segs t TOK.
  Let I66ba4 := AsAllocM2.I66ba4 segs t TOK.
  Let I66ba8 := AsAllocM2.I66ba8 segs t TOK.
  Let I66bb4 := AsAllocM2.I66bb4 segs t TOK.
  Let I66bb8 := AsAllocM2.I66bb8 segs t TOK.
  Let I66bbc := AsAllocM2.I66bbc segs t TOK.
  Let I66bc0 := AsAllocM2.I66bc0 segs t TOK.
  Let I66bf0 := AsAllocM2.I66bf0 segs t TOK.
  Let I66c0c := AsAllocM2.I66c0c segs t TOK.
  Let I66c10 := AsAllocM2.I66c10 segs t TOK.
  Let I66c14 := AsAllocM2.I66c14 segs t TOK.
  Let I66c18 := AsAllocM2.I66c18 segs t TOK.
  Let I66c1c := AsAllocM2.I66c1c segs t TOK.
  Let I66c20 := AsAllocM2.I66c20 segs t TOK.
  Let I66c24 := AsAllocM2.I66c24 segs t TOK.
  Let I66c28 := AsAllocM2.I66c28 segs t TOK.
  Let I66c2c := AsAllocM2.I66c2c segs t TOK.
  Let I66c30 := AsAllocM2.I66c30 segs t TOK.
  Let I66c34 := AsAllocM2.I66c34 segs t TOK.
  Let I66c38 := AsAllocM2.I66c38 segs t TOK.
  Let I66c3c := AsAllocM2.I66c3c segs t TOK.
  Let I66c40 := AsAllocM2.I66c40 segs t TOK.
  Let I66c44 := AsAllocM2.I66c44 segs t TOK.
  Let I66c48 := AsAllocM2.I66c48 segs t TOK.
  Let I66c4c := AsAllocM2.I66c4c segs t TOK.
  Let I66c50 := AsAllocM2.I66c50 segs t TOK.
  Let I66c54 := AsAllocM2.I66c54 segs t TOK.
  Let I66c58 := AsAllocM2.I66c58 segs t TOK.
  Let I66c5c := AsAllocM2.I66c5c segs t TOK.
  Let I66c60 := AsAllocM2.I66c60 segs t TOK.
  Let I66c9c := AsAllocM2.I66c9c segs t TOK.
  Let I66ca0 := AsAllocM2.I66ca0 segs t TOK.
  Let I66ca4 := AsAllocM2.I66ca4 segs t TOK.
  Let I66ca8 := AsAllocM2.I66ca8 segs t TOK.
  Let I66cac := AsAllocM2.I66cac segs t TOK.
  Let I66cb0 := AsAllocM2.I66cb0 segs t TOK.

  Let I66c64 := AsAllocM2.I66c64 segs t TOK.
  Let I66c68 := AsAllocM2.I66c68 segs t TOK.
  Let I66c6c := AsAllocM2.I66c6c segs t TOK.
  Let I66c70 := AsAllocM2.I66c70 segs t TOK.
  Let I66c74 := AsAllocM2.I66c74 segs t TOK.
  Let I66c78 := AsAllocM2.I66c78 segs t TOK.

  Lemma rz2048 : rz n = 2048%Z.
  Proof using Hs. apply AsArith3.rz_big. lia. Qed.

  (* [comment removed for export] *)
  Lemma amA2s : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 49 -> getr r0 21 = Z_to_bv 64 n -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bbbc) M rom) (mkst r (at_ rb 0x4bc90) M rom)
      /\ getr r 19 = Z_to_bv 64 7
      /\ (forall i : reg, In i [2; 8; 9; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using I66bc0 I66bbc I66bb8 I66bb4 I66ba8 I66ba4 I66ba0 I66b94 I66b90 I66b8c I66b80 I66b7c I66b78 I66b6c I66b68 I66b5c I66b58 I66af0 Hs TOK.
    intros M r0 R10 R21 AG0.
    wd_eexists. split.
    { ab_tk I66af0 D_4bbb4 ltac:(condz). an I66b58 D_4bc1c. ab_tk I66b5c D_4bc20 ltac:(condz).
      an I66b68 D_4bc2c. ab_tk I66b6c D_4bc30 ltac:(condz).
      an I66b78 D_4bc3c. an I66b7c D_4bc40. ab_tk I66b80 D_4bc44 ltac:(condz).
      an I66b8c D_4bc50. an I66b90 D_4bc54. ab_tk I66b94 D_4bc58 ltac:(condz).
      an I66ba0 D_4bc64. an I66ba4 D_4bc68. ab_tk I66ba8 D_4bc6c ltac:(condz).
      an I66bb4 D_4bc78. an I66bb8 D_4bc7c. an I66bbc D_4bc80. rewrite v_sltu_lit by lia. replace (n <? 64513)%Z with false by (symmetry; apply Z.ltb_ge; lia).
      an I66bc0 D_4bc84. wd_refl. }
    post; first [ (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
                | intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; reflexivity|]); destruct Hi
                | idtac ].
  Qed.

  (* [comment removed for export] *)
  Lemma amA3cs : forall (M : word -> option byte) r0,
    getr r0 10 = Z_to_bv 64 7 -> getr r0 9 = Z_to_bv 64 0 -> getr r0 19 = Z_to_bv 64 7 -> getr r0 21 = Z_to_bv 64 n -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bcbc) M rom) (mkst r (at_ rb 0x4bcd8) M rom)
      /\ getr r 19 = Z_to_bv 64 7 /\ getr r 10 = Z_to_bv 64 n
      /\ (forall i : reg, In i [2; 8; 18; 20; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using I66cb0 I66cac I66ca8 I66ca4 I66ca0 I66c9c I66bf0 Hs TOK.
    intros M r0 R10 R9 R19 R21 AG0.
    wd_eexists. split.
    { ab_tk I66bf0 D_4bcb4 ltac:(condz).                 (* [comment removed for export] *)
      ab_ft I66c9c D_4bd60 ltac:(condz).                 (* [comment removed for export] *)
      an I66ca0 D_4bd64.                                  (* [comment removed for export] *)
      an I66ca4 D_4bd68.                                  (* [comment removed for export] *)
      an I66ca8 D_4bd6c.                                  (* [comment removed for export] *)
      ab_ft I66cac D_4bd70 ltac:(condz).                 (* [comment removed for export] *)
      an I66cb0 D_4bd74.                                  (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.

  (* [comment removed for export] *)
  Lemma amA4s : forall r0,
    getr r0 19 = Z_to_bv 64 7 -> getr r0 21 = Z_to_bv 64 n -> getr r0 10 = Z_to_bv 64 n -> getr r0 8 = Z_to_bv 64 8 -> getr r0 18 = Z_to_bv 64 8 ->
    getr r0 20 = Z_to_bv 64 65536 -> getr r0 26 = at_ INST 2047 -> getr r0 2 = at_ sp (-144) -> regs_agree CLX regs r0 ->
    exists r, msteps segs (mkst r0 (at_ rb 0x4bcd8) am_m3 rom) (mkst r (at_ rb 0x4bda4) am_m3 rom)
      /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 n /\ getr r 19 = Z_to_bv 64 (sec_needed n) /\ getr r 20 = Z_to_bv 64 2048
      /\ getr r 24 = Z_to_bv 64 18446744073709551608
      /\ (forall i : reg, In i [2; 18; 21; 22; 23; 25; 26; 27] -> getr r i = getr r0 i)
      /\ regs_agree CLX regs r.
  Proof using I66c78 I66c74 I66c70 I66c6c I66c68 I66c64 I66c60 I66c5c I66c58 I66c54 I66c50 I66c4c I66c48 I66c44 I66c40 I66c3c I66c38 I66c34 I66c30 I66c2c I66c28 I66c24 I66c20 I66c1c I66c18 I66c14 I66c10 I66c0c G1 G0 Rmaxsz Hs stk TOK.
    intros r0 R19 R21 R10 R8 R18 R20 R26 R2 AG0. destruct G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). destruct G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI.
    pose proof rz2048 as Hrz.
    assert (Hrd : (rounded n = RoundUp (Z.max n 8) 8)%Z) by reflexivity.
    rewrite Z.max_l in Hrd by lia.
    assert (Hrd2 : (n <= rounded n <= n + 7 /\ rounded n mod 8 = 0)%Z).
    { rewrite Hrd. (lazymatch goal with |- ?G => let G' := eval unfold RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)).
      split; [lia|]. apply Z_mod_mult. }
    assert (Hnd : (needed n = rounded n + 2048)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold needed in G in change_no_check G' end); rewrite Hrz; reflexivity).
    assert (Hsn : (sec_needed n = rounded n + 4096)%Z) by ((lazymatch goal with |- ?G => let G' := eval unfold sec_needed in G in change_no_check G' end); rewrite Hrz; lia).
    wd_eexists. split.
    { av I66c0c D_4bcd0 (Z_to_bv 64 (n + 8)) ltac:(valz).   (* [comment removed for export] *)
      an I66c10 D_4bcd4.                                      (* [comment removed for export] *)
      an I66c14 D_4bcd8.                                      (* [comment removed for export] *)
      av I66c18 D_4bcdc (Z_to_bv 64 (n + 7)) ltac:(valz).    (* [comment removed for export] *)
      an I66c1c D_4bce0.                                      (* [comment removed for export] *)
      an I66c20 D_4bce4.                                      (* [comment removed for export] *)
      match goal with |- context [v_and ?x ?y] => replace (v_and x y) with (Z_to_bv 64 (rounded n)) by ((lazymatch goal with |- ?G => let G' := eval unfold v_and in G in change_no_check G' end); unorm; f_equal; rewrite Hrd; symmetry; apply rounded_val; lia) end.
      an I66c24 D_4bce8.                                      (* [comment removed for export] *)
      av I66c28 D_4bcec (Z_to_bv 64 (rounded n)) ltac:(valz).   (* [comment removed for export] *)
      av I66c2c D_4bcf0 (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_andi in G in change_no_check G' end); change (bv_wrap 64 7) with 7%Z; unorm; rewrite land_7 by lia; replace (rounded n mod 8)%Z with 0%Z by lia; reflexivity).   (* [comment removed for export] *)
      ab_ft I66c30 D_4bcf4 ltac:(condz).                    (* [comment removed for export] *)
      an I66c34 D_4bcf8.                                      (* [comment removed for export] *)
      av I66c38 D_4bcfc (Z_to_bv 64 0) ltac:((lazymatch goal with |- ?G => let G' := eval unfold v_sltiu in G in change_no_check G' end); unorm; change (bv_wrap 64 1) with 1%Z; replace (n <? 1)%Z with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).   (* [comment removed for export] *)
      an I66c3c D_4bd00.                                      (* [comment removed for export] *)
      an I66c40 D_4bd04.                                      (* [comment removed for export] *)   (* [comment removed for export] *)
      an I66c44 D_4bd08.                                      (* [comment removed for export] *)
      av I66c48 D_4bd0c (Z_to_bv 64 n) ltac:(valz).           (* [comment removed for export] *)
      an I66c4c D_4bd10.                                      (* [comment removed for export] *)
      av I66c50 D_4bd14 (Z_to_bv 64 (needed n)) ltac:(rewrite Hnd; valz).   (* [comment removed for export] *)
      an I66c54 D_4bd18. rewrite (v_sltu_lit (needed n) 65537) by lia. replace (needed n <? 65537)%Z with false by (symmetry; apply Z.ltb_ge; lia).   (* [comment removed for export] *)
      an I66c58 D_4bd1c.                                      (* [comment removed for export] *)
      an I66c5c D_4bd20.                                      (* [comment removed for export] *)
      an I66c60 D_4bd24.                                      (* [comment removed for export] *)
      an I66c64 D_4bd28.                                      (* [comment removed for export] *)
      av I66c68 D_4bd2c (Z_to_bv 64 (sec_needed n)) ltac:(rewrite Hsn, Hnd; valz).   (* [comment removed for export] *)
      ab_ft I66c6c D_4bd30 ltac:(condz).                    (* [comment removed for export] *)
      ab_ft I66c70 D_4bd34 ltac:(condz).                    (* [comment removed for export] *)
      cld8 I66c74 D_4bd38 (Z_to_bv 64 (2 ^ 40)) Rmaxsz.      (* [comment removed for export] *)
      ab_tk I66c78 D_4bd3c ltac:(condz).                    (* [comment removed for export] *)
      wd_refl. }
    post.
    all: lazymatch goal with
         | |- regs_agree _ _ _ => (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); ra_chain
         | |- forall x : reg, In x _ -> _ => intros x Hx; cbn [In] in Hx; repeat (destruct Hx as [<-|Hx]; [gres; reflexivity|]); destruct Hx
         | |- _ => idtac
         end.
  Qed.



  Let amA1a := AsAllocM2.amA1a segs t TOK regs mem rom ra sp stk n H1 H2 H10 H11 Hstk G0 G1.
  Let amA1b := AsAllocM2.amA1b segs t TOK regs rom.
  Let amA1c := AsAllocM2.amA1c segs t TOK regs mem rom ra sp stk Rmag Rtbl2 Hstk G0 G1.
  Let amA3a := AsAllocM2.amA3a segs t TOK regs mem rom ra sp stk Rminrz G0 G1.
  Let amA3b := AsAllocM2.amA3b segs t TOK regs mem rom ra sp stk Rmaxrz G0 G1.

  (* [comment removed for export] *)
  Theorem amA_run_s :
    exists r,
      msteps segs (mkst regs (at_ rb 0x4bac8) mem rom) (mkst r (at_ rb 0x4bda4) am_m3 rom)
      /\ getr r 2 = at_ sp (-144) /\ getr r 8 = Z_to_bv 64 0 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = Z_to_bv 64 8
      /\ getr r 19 = Z_to_bv 64 (sec_needed n) /\ getr r 20 = Z_to_bv 64 2048 /\ getr r 21 = Z_to_bv 64 n /\ getr r 22 = INST
      /\ getr r 23 = stk /\ getr r 24 = Z_to_bv 64 18446744073709551608 /\ getr r 25 = Z_to_bv 64 7 /\ getr r 26 = at_ INST 2047
      /\ getr r 27 = Z_to_bv 64 1
      /\ regs_agree CLX regs r.
  Proof using amA3b amA3a amA1c amA1b amA1a I66c78 I66c74 I66c70 I66c6c I66c68 I66c64 I66cb0 I66cac I66ca8 I66ca4 I66ca0 I66c9c I66c60 I66c5c I66c58 I66c54 I66c50 I66c4c I66c48 I66c44 I66c40 I66c3c I66c38 I66c34 I66c30 I66c2c I66c28 I66c24 I66c20 I66c1c I66c18 I66c14 I66c10 I66c0c I66bf0 I66bc0 I66bbc I66bb8 I66bb4 I66ba8 I66ba4 I66ba0 I66b94 I66b90 I66b8c I66b80 I66b7c I66b78 I66b6c I66b68 I66b5c I66b58 I66af0 am_m2_outside am_m1_outside RETa G1 G0 Hstk Rmaxsz Rmaxrz Rminrz Rt2048 Rt16 Rtbl2 Rmag Rrss Rinited Hs H11 H10 H2 H1 TOK.
    pose proof G0 as (Ga & Gb & Gc & Gd & Ge & Gf & Gg). pose proof G1 as [G1a G1b].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range INST) as HI. pose proof (u64_range (am_tbl t)) as HT.
    pose proof TOK as TOK'. destruct TOK' as [_ _ _ _ _ AIN AINB RSS RSSB RZL RZM RZT RB].
    Ltac via AG r H := let T := fresh in pose proof (AG r ltac:(notin_list)) as T; rewrite H in T; exact T.
    Ltac viaK K AG r H := rewrite (K r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); via AG r H.
    (* [comment removed for export] *)
    destruct amA1a as (r1 & RUN1 & A1 & A2 & A9 & A27 & A23 & A18 & A21 & A22 & AG1).
    (* [comment removed for export] *)
    destruct (ain_run segs rb (am_g_inited t) AIN AINB am_m1 rom r1 (at_ rb 0x4bb78)) as (r2 & RUN2 & B10 & AG2).
    { rewrite <- Rinited. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact A1. }
    (* [comment removed for export] *)
    destruct (amA1b am_m1 r2 B10 ltac:(eapply regs_agree_trans; [exact AG1 | regs_agree_weaken AG2])) as (r3 & RUN3 & C1 & CK & AG3).
    (* [comment removed for export] *)
    destruct (rss_run segs rb (am_g_rss t) RSS RSSB am_m1 rom r3 (at_ rb 0x4bb80)) as (r4 & RUN4 & D10 & AG4).
    { rewrite <- Rrss. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m1_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    { apply RETa; [reflexivity | lia]. }
    { exact C1. }
    (* [comment removed for export] *)
    destruct (amA1c r4 D10) as (r5 & RUN5 & E10 & E8 & E25 & E26 & EK & AG5).
    { rewrite (AG4 2) by notin_list. viaK CK AG2 (2:reg) A2. }
    { rewrite (AG4 23) by notin_list. viaK CK AG2 (23:reg) A23. }
    { rewrite (AG4 18) by notin_list. viaK CK AG2 (18:reg) A18. }
    { rewrite (AG4 22) by notin_list. viaK CK AG2 (22:reg) A22. }
    { rewrite (AG4 9) by notin_list. viaK CK AG2 (9:reg) A9. }
    { eapply regs_agree_trans; [exact AG3 | regs_agree_weaken AG4]. }
    assert (E21 : getr r5 21 = Z_to_bv 64 n). { rewrite (EK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG4 21) by notin_list. viaK CK AG2 (21:reg) A21. }
    Ltac thr5 EK AG4 CK AG2 r A := rewrite (EK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG4 r) by notin_list; rewrite (CK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); let T := fresh in pose proof (AG2 r ltac:(notin_list)) as T; rewrite A in T; exact T.
    assert (E2 : getr r5 2 = at_ sp (-144)) by (thr5 EK AG4 CK AG2 (2:reg) A2).
    assert (E9 : getr r5 9 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (9:reg) A9).
    assert (E18 : getr r5 18 = Z_to_bv 64 8) by (thr5 EK AG4 CK AG2 (18:reg) A18).
    assert (E22 : getr r5 22 = INST) by (thr5 EK AG4 CK AG2 (22:reg) A22).
    assert (E23 : getr r5 23 = stk) by (thr5 EK AG4 CK AG2 (23:reg) A23).
    assert (E27 : getr r5 27 = Z_to_bv 64 1) by (thr5 EK AG4 CK AG2 (27:reg) A27).
    (* [comment removed for export] *)
    destruct (amA2s am_m2 r5 E10 E21 AG5) as (r6 & RUN6 & F19 & FK & AG6).
    (* [comment removed for export] *)
    destruct (amA3a r6 ltac:(rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E26) ltac:(rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) AG6) as (r7 & RUN7 & G1' & G10 & G20 & G24 & GK & AG7).
    (* [comment removed for export] *)
    assert (Rm2 : rdn segs am_m2 (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply am_m2_outside; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt2 : rdn segs am_m2 (at_ (am_tbl t) 8) 1 = Some [Z_to_bv 8 4]).
    { rewrite <- Rt16. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply am_m2_outside; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK2 : store_ok segs am_m2 (at_ (at_ sp (-144)) (-8)) 8 = true).
    { rewrite at_at. (lazymatch goal with |- ?G => let G' := eval unfold am_m2, am_m1 in G in change_no_check G' end). repeat (eapply store_ok_mono; [apply wbytes_grows|]).
      eapply (store_ok_sub segs mem (at_ sp (-160)) _ 160); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (rzl16_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT am_m2 rom r7 (at_ rb 0x4bca8) (at_ sp (-144)) Rm2 ltac:(lia) SOK2
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4bca8 eq_refl ltac:(lia)) G1' ltac:(rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt2 G10)
      as (r8 & RUN8 & H10' & AG8).
    unfold rzM1 in RUN8. rewrite at_at in RUN8. cbn [Z.add] in RUN8.
    (* [comment removed for export] *)
    destruct (amA3b r8 H10') as (r9 & RUN9 & I1 & I10 & I9 & IK & AG9).
    { rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { rewrite (AG8 2) by notin_list. rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E2. }
    { rewrite (AG8 24) by notin_list. exact G24. }
    { eapply regs_agree_trans; [exact AG7 | regs_agree_weaken AG8]. }
    (* [comment removed for export] *)
    set (M3a := wbytes am_m2 (at_ sp (-152)) (LE8 (at_ rb 0x4bca8))) in *.
    assert (HM3a : forall x : word, (U x < U sp - 152 \/ U sp <= U x)%Z -> M3a x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). rewrite wbytes_outside; [apply am_m2_outside; lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rm3 : rdn segs M3a (Z_to_bv 64 (am_g_magic t)) 8 = Some (LE8 MAGICw)).
    { rewrite <- Rmag. apply rdn_ext; [wd_ulia_c | intros x Hx; apply HM3a; revert Hx; unorm; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); intros Hx; lia]. }
    assert (Rt3 : rdn segs M3a (at_ (am_tbl t) 49) 1 = Some [Z_to_bv 8 11]).
    { rewrite <- Rt2048. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply HM3a; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOK3 : store_ok segs M3a (at_ (at_ sp (-144)) (-8)) 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M3a in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOK2]. }
    destruct (rzl2048_run segs rb RB (am_g_magic t) (am_tbl t) RZL RZM RZT M3a rom r9 (at_ rb 0x4bcbc) (at_ sp (-144)) Rm3 ltac:(lia) SOK3
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(right; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ])
                (RETa 0x4bcbc eq_refl ltac:(lia)) I1 ltac:(rewrite (IK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 2) by notin_list; rewrite (GK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E2) Rt3 I10)
      as (r10 & RUN10 & J10 & AG10).
    unfold rzM1 in RUN10. rewrite at_at in RUN10. cbn [Z.add] in RUN10.
    change (wbytes M3a (at_ sp (-152)) (LE8 (at_ rb 0x4bcbc))) with am_m3 in RUN10.
    (* [comment removed for export] *)
    destruct (amA3cs am_m3 r10 J10) as (r11 & RUN11 & K19 & K10 & KK & AG11).
    { rewrite (AG10 9) by notin_list. exact I9. }
    { rewrite (AG10 19) by notin_list. rewrite (IK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 19) by notin_list. rewrite (GK 19) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact F19. }
    { rewrite (AG10 21) by notin_list. rewrite (IK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 21) by notin_list. rewrite (GK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 21) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E21. }
    { eapply regs_agree_trans; [exact AG9 | regs_agree_weaken AG10]. }
    (* [comment removed for export] *)
    Ltac thrB KK AG10 IK AG8 GK FK r H := rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    destruct (amA4s r11 K19) as (r12 & RUN12 & L8 & L9 & L19 & L20 & L24 & LK & AG12).
    { thrB KK AG10 IK AG8 GK FK (21:reg) E21. }
    { exact K10. }
    { rewrite (KK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 8) by notin_list. rewrite (IK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 8) by notin_list. rewrite (GK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 8) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E8. }
    { thrB KK AG10 IK AG8 GK FK (18:reg) E18. }
    { rewrite (KK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 20) by notin_list. rewrite (IK 20) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 20) by notin_list. exact G20. }
    { rewrite (KK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG10 26) by notin_list. rewrite (IK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (AG8 26) by notin_list. rewrite (GK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). rewrite (FK 26) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]). exact E26. }
    { thrB KK AG10 IK AG8 GK FK (2:reg) E2. }
    { eapply regs_agree_trans; [exact AG11 | idtac]. apply regs_agree_refl. }
    exists r12. split.
    { eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|]. eapply msteps_trans; [exact RUN4|].
      eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|]. eapply msteps_trans; [exact RUN8|].
      eapply msteps_trans; [exact RUN9|]. eapply msteps_trans; [exact RUN10|]. eapply msteps_trans; [exact RUN11 | exact RUN12]. }
    Ltac thrC LK KK AG10 IK AG8 GK FK r H := rewrite (LK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 r) by notin_list; rewrite (IK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]);
                                        rewrite (AG8 r) by notin_list; rewrite (GK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK r) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact H.
    split; [thrC LK KK AG10 IK AG8 GK FK (2:reg) E2|]. split; [exact L8|]. split; [exact L9|]. split; [thrC LK KK AG10 IK AG8 GK FK (18:reg) E18|].
    split; [exact L19|]. split; [exact L20|]. split; [thrC LK KK AG10 IK AG8 GK FK (21:reg) E21|]. split; [thrC LK KK AG10 IK AG8 GK FK (22:reg) E22|].
    split; [thrC LK KK AG10 IK AG8 GK FK (23:reg) E23|]. split; [exact L24|].
    split; [rewrite (LK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (KK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG10 25) by notin_list; rewrite (IK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (AG8 25) by notin_list; rewrite (GK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); rewrite (FK 25) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); first [ solve [repeat (first [left; reflexivity | right])] | tauto ]); exact E25|].
    split; [thrC LK KK AG10 IK AG8 GK FK (26:reg) E26|].
    split; [thrC LK KK AG10 IK AG8 GK FK (27:reg) E27|].
    exact AG12.
  Qed.

End AMS.
End FPGen1.
End AsAllocM2s.
Require LinuxProcessSemantics.Riscv.Sem OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM7j.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section RFJ.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma R509c4 : fetch_word segs (at_ rb 0x509cc) = Some W_509c4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 0 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509c8 : fetch_word segs (at_ rb 0x509d0) = Some W_509c8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 1 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509cc : fetch_word segs (at_ rb 0x509d4) = Some W_509cc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 2 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d0 : fetch_word segs (at_ rb 0x509d8) = Some W_509d0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 3 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d4 : fetch_word segs (at_ rb 0x509dc) = Some W_509d4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 4 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509d8 : fetch_word segs (at_ rb 0x509e0) = Some W_509d8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 5 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509dc : fetch_word segs (at_ rb 0x509e4) = Some W_509dc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 6 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e0 : fetch_word segs (at_ rb 0x509e8) = Some W_509e0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 7 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e4 : fetch_word segs (at_ rb 0x509ec) = Some W_509e4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 8 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509e8 : fetch_word segs (at_ rb 0x509f0) = Some W_509e8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 9 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509ec : fetch_word segs (at_ rb 0x509f4) = Some W_509ec.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 10 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f0 : fetch_word segs (at_ rb 0x509f8) = Some W_509f0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 11 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f4 : fetch_word segs (at_ rb 0x509fc) = Some W_509f4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 12 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509f8 : fetch_word segs (at_ rb 0x50a00) = Some W_509f8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 13 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R509fc : fetch_word segs (at_ rb 0x50a04) = Some W_509fc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 14 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a00 : fetch_word segs (at_ rb 0x50a08) = Some W_50a00.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 15 _ HRF eq_refl). Qed.






   (* [comment removed for export] *)
  Lemma R50a20 : fetch_word segs (at_ rb 0x50a28) = Some W_50a20.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 23 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a24 : fetch_word segs (at_ rb 0x50a2c) = Some W_50a24.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 24 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a28 : fetch_word segs (at_ rb 0x50a30) = Some W_50a28.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 25 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a2c : fetch_word segs (at_ rb 0x50a34) = Some W_50a2c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 26 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a30 : fetch_word segs (at_ rb 0x50a38) = Some W_50a30.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 27 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a34 : fetch_word segs (at_ rb 0x50a3c) = Some W_50a34.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 28 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a38 : fetch_word segs (at_ rb 0x50a40) = Some W_50a38.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 29 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a3c : fetch_word segs (at_ rb 0x50a44) = Some W_50a3c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 30 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a40 : fetch_word segs (at_ rb 0x50a48) = Some W_50a40.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 31 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a44 : fetch_word segs (at_ rb 0x50a4c) = Some W_50a44.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 32 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a48 : fetch_word segs (at_ rb 0x50a50) = Some W_50a48.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 33 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a4c : fetch_word segs (at_ rb 0x50a54) = Some W_50a4c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 34 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a50 : fetch_word segs (at_ rb 0x50a58) = Some W_50a50.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 35 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a54 : fetch_word segs (at_ rb 0x50a5c) = Some W_50a54.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 36 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a58 : fetch_word segs (at_ rb 0x50a60) = Some W_50a58.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 37 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a5c : fetch_word segs (at_ rb 0x50a64) = Some W_50a5c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 38 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a60 : fetch_word segs (at_ rb 0x50a68) = Some W_50a60.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 39 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a64 : fetch_word segs (at_ rb 0x50a6c) = Some W_50a64.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 40 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a68 : fetch_word segs (at_ rb 0x50a70) = Some W_50a68.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 41 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a6c : fetch_word segs (at_ rb 0x50a74) = Some W_50a6c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 42 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a70 : fetch_word segs (at_ rb 0x50a78) = Some W_50a70.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 43 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a74 : fetch_word segs (at_ rb 0x50a7c) = Some W_50a74.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 44 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a78 : fetch_word segs (at_ rb 0x50a80) = Some W_50a78.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 45 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a7c : fetch_word segs (at_ rb 0x50a84) = Some W_50a7c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 46 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a80 : fetch_word segs (at_ rb 0x50a88) = Some W_50a80.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 47 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a84 : fetch_word segs (at_ rb 0x50a8c) = Some W_50a84.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 48 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a88 : fetch_word segs (at_ rb 0x50a90) = Some W_50a88.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 49 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a8c : fetch_word segs (at_ rb 0x50a94) = Some W_50a8c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 50 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a90 : fetch_word segs (at_ rb 0x50a98) = Some W_50a90.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 51 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a94 : fetch_word segs (at_ rb 0x50a9c) = Some W_50a94.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 52 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a98 : fetch_word segs (at_ rb 0x50aa0) = Some W_50a98.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 53 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50a9c : fetch_word segs (at_ rb 0x50aa4) = Some W_50a9c.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 54 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa0 : fetch_word segs (at_ rb 0x50aa8) = Some W_50aa0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 55 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa4 : fetch_word segs (at_ rb 0x50aac) = Some W_50aa4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 56 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aa8 : fetch_word segs (at_ rb 0x50ab0) = Some W_50aa8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 57 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50aac : fetch_word segs (at_ rb 0x50ab4) = Some W_50aac.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 58 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab0 : fetch_word segs (at_ rb 0x50ab8) = Some W_50ab0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 59 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab4 : fetch_word segs (at_ rb 0x50abc) = Some W_50ab4.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 60 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ab8 : fetch_word segs (at_ rb 0x50ac0) = Some W_50ab8.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 61 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50abc : fetch_word segs (at_ rb 0x50ac4) = Some W_50abc.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 62 _ HRF eq_refl). Qed.   (* [comment removed for export] *)
  Lemma R50ac0 : fetch_word segs (at_ rb 0x50ac8) = Some W_50ac0.  Proof using HRF. exact (code_ato_get segs rb 0x509cc rf_words 63 _ HRF eq_refl). Qed.   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache pc alloc : word) (c : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = cache.
  Hypothesis H11 : getr regs 11 = pc.
  Hypothesis H12 : getr regs 12 = alloc.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 c.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-32)) 32 = true.
  Hypothesis G1 : (2 ^ 32 + 32 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gpc : (U cache + 2640 <= U sp - 32)%Z /\ (U pc = U cache + 80 * c)%Z /\ (1 <= c <= 30)%Z.
  Hypothesis HTW : store_ok segs mem (at_ cache 80) 2480 = true.      (* [comment removed for export] *)
  #[local] Abbreviation RFM1 := (rf_m1 regs mem ra sp).
  #[local] Abbreviation ICM k := (ic_mem regs mem ra sp cache k).

  Ltac sokS Hs0 lo N :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub segs mem lo _ N); [rewrite at_u; lia | exact Hs0 | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsd8 F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokS Hstk (at_ sp (-32)) 32%nat ]
      | step_simpl]; vn.
  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].
  (* [comment removed for export] *)
  Ltac grows_ic := lazymatch goal with
    | |- mem_grows ?m ?m => apply mem_grows_refl
    | |- mem_grows _ (wbytes _ _ _) => eapply mem_grows_trans; [|apply wbytes_grows]; grows_ic
    | |- mem_grows _ (ic_mem _ _ _ _ _ _) => apply ic_mem_grows
    | |- mem_grows _ (rf_m1 _ _ _ _) => apply rf_m1_grows
    end.
  Ltac sokT := eapply (store_ok_mono segs _ mem); [grows_ic|];
    eapply (store_ok_sub segs mem (at_ cache 80) _ 2480%nat); [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ] | exact HTW | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ] | rewrite !at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia].
  Ltac fsw4 F D aa :=
    chain_step; [reflexivity
      | eapply step_sw_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokT ]
      | step_simpl]; vn.
  Ltac fsd8c F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; rwH; imm_norm; rewrite ?at_addi; first [reflexivity | f_equal; lia]
        | gres; rwH; reflexivity
        | sokT ]
      | step_simpl]; vn.
  (* [comment removed for export] *)
  Ltac icK Hx := first [ gres_frame Hx | repeat (rewrite getr_other; [| let E := fresh in intros E; apply Hx; rewrite E; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto]); reflexivity ].

  Lemma ic_20_23 : forall r,
      getr r 11 = at_ cache 1608 -> getr r 13 = Z_to_bv 64 640 -> getr r 15 = Z_to_bv 64 4 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 19) rom) (mkst r' (at_ rb 0x50a70) (ICM 23) rom)
        /\ (getr r' 11 = at_ cache 1928 /\ getr r' 13 = Z_to_bv 64 768 /\ getr r' 15 = Z_to_bv 64 8 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1604). fsd8c R50a5c D_50a5c (at_ cache 1608).
      change (wbytes (wbytes (ICM 19) _ _) _ _) with (ICM 20).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1684). fsd8c R50a5c D_50a5c (at_ cache 1688).
      change (wbytes (wbytes (ICM 20) _ _) _ _) with (ICM 21).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1764). fsd8c R50a5c D_50a5c (at_ cache 1768).
      change (wbytes (wbytes (ICM 21) _ _) _ _) with (ICM 22).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1844). fsd8c R50a5c D_50a5c (at_ cache 1848).
      change (wbytes (wbytes (ICM 22) _ _) _ _) with (ICM 23).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_24_27 : forall r,
      getr r 11 = at_ cache 1928 -> getr r 13 = Z_to_bv 64 768 -> getr r 15 = Z_to_bv 64 8 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 23) rom) (mkst r' (at_ rb 0x50a70) (ICM 27) rom)
        /\ (getr r' 11 = at_ cache 2248 /\ getr r' 13 = Z_to_bv 64 896 /\ getr r' 15 = Z_to_bv 64 12 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 1924). fsd8c R50a5c D_50a5c (at_ cache 1928).
      change (wbytes (wbytes (ICM 23) _ _) _ _) with (ICM 24).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 2004). fsd8c R50a5c D_50a5c (at_ cache 2008).
      change (wbytes (wbytes (ICM 24) _ _) _ _) with (ICM 25).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 2084). fsd8c R50a5c D_50a5c (at_ cache 2088).
      change (wbytes (wbytes (ICM 25) _ _) _ _) with (ICM 26).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 2164). fsd8c R50a5c D_50a5c (at_ cache 2168).
      change (wbytes (wbytes (ICM 26) _ _) _ _) with (ICM 27).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_28_30 : forall r,
      getr r 11 = at_ cache 2248 -> getr r 13 = Z_to_bv 64 896 -> getr r 15 = Z_to_bv 64 12 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 27) rom) (mkst r' (at_ rb 0x50a70) (ICM 30) rom)
        /\ (getr r' 11 = at_ cache 2488 /\ getr r' 13 = Z_to_bv 64 992 /\ getr r' 15 = Z_to_bv 64 15 /\ getr r' 16 = Z_to_bv 64 15 /\ getr r' 17 = Z_to_bv 64 1024 /\ getr r' 5 = Z_to_bv 64 16 /\ getr r' 6 = Z_to_bv 64 17 /\ getr r' 7 = Z_to_bv 64 512)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split; [|split].
    -
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 2244). fsd8c R50a5c D_50a5c (at_ cache 2248).
      change (wbytes (wbytes (ICM 27) _ _) _ _) with (ICM 28).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 2324). fsd8c R50a5c D_50a5c (at_ cache 2328).
      change (wbytes (wbytes (ICM 28) _ _) _ _) with (ICM 29).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      (* [comment removed for export] *)
      ab_ft R50a68 D_50a68 ltac:(condz). an R50a6c D_50a6c. an R50a70 D_50a70. ab_ft R50a74 D_50a74 ltac:(condz).
      an R50a78 D_50a78. an R50a7c D_50a7c. an R50a80 D_50a80. an R50a84 D_50a84. an R50a88 D_50a88. an R50a8c D_50a8c. an R50a90 D_50a90.
      an R50a94 D_50a94. an R50a98 D_50a98. ab_tk R50a9c D_50a9c ltac:(condz).
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 2404). fsd8c R50a5c D_50a5c (at_ cache 2408).
      change (wbytes (wbytes (ICM 29) _ _) _ _) with (ICM 30).
      an R50a60 D_50a60.
      ab_ft R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - repeat split; gres; first [reflexivity | assumption].
    - intros x Hx. gres. icK Hx.
  Qed.

  Lemma ic_31 : forall r,
      getr r 11 = at_ cache 2488 -> getr r 13 = Z_to_bv 64 992 -> getr r 15 = Z_to_bv 64 15 -> getr r 16 = Z_to_bv 64 15 -> getr r 17 = Z_to_bv 64 1024 -> getr r 5 = Z_to_bv 64 16 -> getr r 6 = Z_to_bv 64 17 -> getr r 7 = Z_to_bv 64 512 ->
      exists r', msteps segs (mkst r (at_ rb 0x50a70) (ICM 30) rom) (mkst r' (at_ rb 0x50ac4) (ICM 31) rom)
        /\ (forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r' x = getr r x).
  Proof using HTW Gpc G1 c pc RB HRF.
    intros r Q11 Q13 Q15 Q16 Q17 Q5 Q6 Q7.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    wd_eexists. split.
    -
      (* [comment removed for export] *)
      ab_tk R50a68 D_50a68 ltac:(condz). an R50aa8 D_50aa8. an R50aac D_50aac. an R50ab0 D_50ab0. ab_ft R50ab4 D_50ab4 ltac:(condz). an R50ab8 D_50ab8. an R50aa0 D_50aa0. an R50aa4 D_50aa4.
      an R50a44 D_50a44. an R50a48 D_50a48. an R50a4c D_50a4c. an R50a50 D_50a50. an R50a54 D_50a54.
      fsw4 R50a58 D_50a58 (at_ cache 2484). fsd8c R50a5c D_50a5c (at_ cache 2488).
      change (wbytes (wbytes (ICM 30) _ _) _ _) with (ICM 31).
      an R50a60 D_50a60.
      ab_tk R50a64 D_50a64 ltac:(condz).
      wd_refl.
    - intros x Hx. gres. icK Hx.
  Qed.


  (* [comment removed for export] *)
  Lemma rf_pro0 :
    rdn segs mem (at_ pc 4) 4 = Some (LE4 0) ->
    exists r,
      msteps segs (mkst regs (at_ rb 0x509cc) mem rom) (mkst r (at_ rb 0x50acc) (ICM 31) rom)
      /\ getr r 1 = at_ rb 0x50a0c /\ getr r 2 = at_ sp (-32) /\ getr r 8 = pc /\ getr r 9 = Z_to_bv 64 (icmc c / 2)
      /\ getr r 10 = alloc /\ getr r 11 = at_ cache 2560 /\ getr r 12 = Z_to_bv 64 c /\ getr r 13 = at_ pc 16 /\ getr r 14 = Z_to_bv 64 (icmc c / 2)
      /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]) regs r.
  Proof using HTW Gpc G1 Hstk H13 H12 H11 H10 H2 H1 RB HRF.
    intros Rmc0.
    destruct G1 as [G1a G1b]. destruct Gpc as (Gp1 & Gp2 & Gp3). pose proof (u64_range sp) as Hspr. pose proof (u64_range cache). pose proof (u64_range pc).
    pose proof (icmc_range c ltac:(lia)) as [Ic1 Ic2].
    (* [comment removed for export] *)
    assert (P0 : exists r0, msteps segs (mkst regs (at_ rb 0x509cc) mem rom) (mkst r0 (at_ rb 0x50a70) (ICM 0) rom)
              /\ (getr r0 11 = at_ cache 88 /\ getr r0 13 = Z_to_bv 64 32 /\ getr r0 15 = Z_to_bv 64 18446744073709551601 /\ getr r0 16 = Z_to_bv 64 15
                  /\ getr r0 17 = Z_to_bv 64 1024 /\ getr r0 5 = Z_to_bv 64 16 /\ getr r0 6 = Z_to_bv 64 17 /\ getr r0 7 = Z_to_bv 64 512)
              /\ getr r0 2 = at_ sp (-32) /\ getr r0 8 = pc /\ getr r0 10 = cache /\ getr r0 12 = alloc /\ getr r0 14 = Z_to_bv 64 c
              /\ regs_agree (fun i : reg => In i [1; 2; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30]) regs r0).
    { wd_eexists. split; [|split; [|split; [|split; [|split; [|split; [|split]]]]]].
      - an R509c4 D_509c4.                                   (* [comment removed for export] *)
        fsd8 R509c8 D_509c8 (at_ sp (-8)).                   (* [comment removed for export] *)
        fsd8 R509cc D_509cc (at_ sp (-16)).                  (* [comment removed for export] *)
        fsd8 R509d0 D_509d0 (at_ sp (-24)).                  (* [comment removed for export] *)
        change (wbytes _ _ _) with RFM1.
        an R509d4 D_509d4.                                   (* [comment removed for export] *)
        an R509d8 D_509d8.                                   (* [comment removed for export] *)
        chain_step; [reflexivity
          | eapply step_lw with (bs := LE4 0) (v := Z_to_bv 64 0);
            [exact R509dc | reflexivity | exact D_509dc
            | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at;
              rewrite <- Rmc0; apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply (rf_m1_outside rb regs mem ra sp G1); rewrite at_u in Hx by lia; cbn in Hx; lia]
            | apply bytes4_small; lia]
          | step_simpl]; rewrite (v_lw_small 0) by lia; vn.   (* [comment removed for export] *)
        ab_tk R509e0 D_509e0 ltac:(condz).                  (* [comment removed for export] *)
        an R50a20 D_50a20.                                   (* [comment removed for export] *)
        an R50a24 D_50a24. an R50a28 D_50a28. an R50a2c D_50a2c. an R50a30 D_50a30.   (* [comment removed for export] *)
        an R50a34 D_50a34. an R50a38 D_50a38. an R50a3c D_50a3c.                      (* [comment removed for export] *)
        an R50a40 D_50a40.                                   (* [comment removed for export] *)
        wd_refl.
      - repeat split; gres; reflexivity.
      - gres; reflexivity. - gres; rwH; reflexivity. - gres; rwH; reflexivity. - gres; rwH; reflexivity. - gres; rwH; reflexivity.
      - ra_solve. }
    destruct P0 as (r0 & RUN0 & (A11 & A13 & A15 & A16 & A17 & A5 & A6 & A7) & A2 & A8 & A10 & A12 & A14 & AK).
    Ltac icstep L r A11 A13 A15 A16 A17 A5 A6 A7 :=
      destruct (L r A11 A13 A15 A16 A17 A5 A6 A7) as (?r & ?RUN & (?B11 & ?B13 & ?B15 & ?B16 & ?B17 & ?B5 & ?B6 & ?B7) & ?BK).
    destruct (ic_1_5 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r0 A11 A13 A15 A16 A17 A5 A6 A7) as (r1 & RUN1 & (B11 & B13 & B15 & B16 & B17 & B5 & B6 & B7) & BK1).
    destruct (ic_6_10 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r1 B11 B13 B15 B16 B17 B5 B6 B7) as (r2 & RUN2 & (C11 & C13 & C15 & C16 & C17 & C5 & C6 & C7) & BK2).
    destruct (ic_11_15 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r2 C11 C13 C15 C16 C17 C5 C6 C7) as (r3 & RUN3 & (D11 & D13 & D15 & D16 & D17 & D5 & D6 & D7) & BK3).
    destruct (ic_16_19 segs rb HRF RB regs mem rom ra sp cache pc c G1 Gpc HTW r3 D11 D13 D15 D16 D17 D5 D6 D7) as (r4 & RUN4 & (E11 & E13 & E15 & E16 & E17 & E5 & E6 & E7) & BK4).
    destruct (ic_20_23 r4 E11 E13 E15 E16 E17 E5 E6 E7) as (r5 & RUN5 & (F11 & F13 & F15 & F16 & F17 & F5 & F6 & F7) & BK5).
    destruct (ic_24_27 r5 F11 F13 F15 F16 F17 F5 F6 F7) as (r6 & RUN6 & (I11 & I13 & I15 & I16 & I17 & I5 & I6 & I7) & BK6).
    destruct (ic_28_30 r6 I11 I13 I15 I16 I17 I5 I6 I7) as (r7 & RUN7 & (J11 & J13 & J15 & J16 & J17 & J5 & J6 & J7) & BK7).
    destruct (ic_31 r7 J11 J13 J15 J16 J17 J5 J6 J7) as (r8 & RUN8 & BK8).
    assert (KK : forall x : reg, ~ In x [11; 13; 15; 16; 17; 5; 6; 7; 28; 29; 30] -> getr r8 x = getr r0 x).
    { intros x Hx. rewrite (BK8 x Hx), (BK7 x Hx), (BK6 x Hx), (BK5 x Hx), (BK4 x Hx), (BK3 x Hx), (BK2 x Hx). exact (BK1 x Hx). }
    assert (K2 : getr r8 2 = at_ sp (-32)) by (rewrite KK by notin; exact A2).
    assert (K8 : getr r8 8 = pc) by (rewrite KK by notin; exact A8).
    assert (K10 : getr r8 10 = cache) by (rewrite KK by notin; exact A10).
    assert (K12 : getr r8 12 = alloc) by (rewrite KK by notin; exact A12).
    assert (K14 : getr r8 14 = Z_to_bv 64 c) by (rewrite KK by notin; exact A14).
    assert (Rmc31 : rdn segs (ICM 31) (at_ pc 4) 4 = Some (LE4 (icmc c))).
    { replace (at_ pc 4) with (at_ cache (80 * c + 4)) by (apply bv_eq; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite !at_u by lia; lia ]). apply (ic_mem_mc segs rb regs mem ra sp cache pc c G1 Gpc); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia. }
    wd_eexists. split.
    - eapply msteps_trans; [exact RUN0|]. eapply msteps_trans; [exact RUN1|]. eapply msteps_trans; [exact RUN2|]. eapply msteps_trans; [exact RUN3|].
      eapply msteps_trans; [exact RUN4|]. eapply msteps_trans; [exact RUN5|]. eapply msteps_trans; [exact RUN6|]. eapply msteps_trans; [exact RUN7|].
      eapply msteps_trans; [exact RUN8|].
      chain_step; [reflexivity
        | eapply step_lw with (bs := LE4 (icmc c)) (v := Z_to_bv 64 (icmc c));
          [exact R50abc | reflexivity | exact D_50abc
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; exact Rmc31
          | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small (icmc c)) by lia; vn.   (* [comment removed for export] *)
      an R50ac0 D_50ac0.                                   (* [comment removed for export] *)
      an R509e4 D_509e4. rewrite (v_srliw1_small (icmc c)) by lia.   (* [comment removed for export] *)
      an R509e8 D_509e8.                                   (* [comment removed for export] *)
      av R509ec D_509ec (at_ cache 2560) ltac:(rewrite ?at_at; vz).   (* [comment removed for export] *)
      av R509f0 D_509f0 (at_ pc 16) ltac:(vz).            (* [comment removed for export] *)
      an R509f4 D_509f4.                                   (* [comment removed for export] *)
      an R509f8 D_509f8.                                   (* [comment removed for export] *)
      an R509fc D_509fc.                                   (* [comment removed for export] *)
      an R50a00 D_50a00.                                   (* [comment removed for export] *)
      wd_refl.
    - post.
      repeat (first [ apply regs_agree_upd; [solve [in_list] |]
                    | apply regs_agree_upd_keep; [ | first [reflexivity | rwH; rewrite ?at_0; reflexivity | symmetry; assumption] | let X := fresh in intros X; discriminate X ] ]).
      intros x Hx. rewrite KK; [exact (AK x Hx)|]. intros Hin. apply Hx. cbn [In] in Hin |- *. first [ solve [clear - Hin; tauto] | tauto ].
  Qed.

End RFJ.
End FPGen1.
End AsAllocM7j.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM7r.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i AsAllocM7j.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section RFR.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis HGF : code_ato segs rb 0x50acc gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x50c74 0x50c84 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache pc alloc : word) (c mc SPB nf : Z) (msk stv : word) (faf : Z -> Z).
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * c)%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (SPB + 2 ^ 37 + 128 * c)).
  #[local] Abbreviation FABz := (SPB + c * 2 ^ 32 + 3758096384)%Z.
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = cache.
  Hypothesis H11 : getr regs 11 = pc.
  Hypothesis H12 : getr regs 12 = alloc.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 c.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-160)) 160 = true.          (* [comment removed for export] *)
  Hypothesis G1 : (SPB + 2 ^ 37 + 4096 + 160 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gpc : (U cache + 2640 <= U sp - 160)%Z /\ (U pc = U cache + 80 * c)%Z /\ (1 <= c <= 30)%Z /\ (U cache mod 4 = 0)%Z.
  (* [comment removed for export] *)
  Hypothesis GcT : (U cache + 2640 <= SPB \/ SPB + 2 ^ 37 + 4096 <= U cache)%Z.
  Hypothesis GcI : (AIMGHI <= U cache \/ U cache + 2640 <= AIMGLO)%Z.
  Hypothesis Galloc : (AIMGLO <= U alloc /\ U alloc + 56 <= AIMGHI)%Z.
  Hypothesis GSPB : (0 <= SPB)%Z /\ (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z.
  (* [comment removed for export] *)
  Hypothesis Rspb : rdn segs mem (at_ alloc 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  Hypothesis Rrib : rdn segs mem (at_ alloc 48) 8 = Some (LE8 (Z_to_bv 64 (SPB + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis SOKpc : store_ok segs mem pc 48 = true.






End RFR.
End FPGen1.
End AsAllocM7r.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocM3m.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM7r.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= am_lia.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Definition cbm_words : list (option (bv 32)) :=
  [Some W_50504; Some W_50508; Some W_5050c; Some W_50510; Some W_50514; Some W_50518; Some W_5051c; Some W_50520;
   Some W_50524; Some W_50528; Some W_5052c; Some W_50530; Some W_50534; Some W_50538; Some W_5053c; Some W_50540;
   Some W_50544; Some W_50548]%list.

(* [comment removed for export] *)
Definition cbm_clob : list reg := [5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30].

Section CBM.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HCB : code_ato segs rb 0x5027c cb_words.
  Hypothesis HCBM : code_ato segs rb 0x5050c cbm_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.

  Lemma J50408 : fetch_word segs (at_ rb 0x50410) = Some W_50408.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 101 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5040c : fetch_word segs (at_ rb 0x50414) = Some W_5040c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 102 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50410 : fetch_word segs (at_ rb 0x50418) = Some W_50410.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 103 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50414 : fetch_word segs (at_ rb 0x5041c) = Some W_50414.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 104 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50418 : fetch_word segs (at_ rb 0x50420) = Some W_50418.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 105 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5041c : fetch_word segs (at_ rb 0x50424) = Some W_5041c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 106 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50420 : fetch_word segs (at_ rb 0x50428) = Some W_50420.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 107 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50424 : fetch_word segs (at_ rb 0x5042c) = Some W_50424.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 108 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50428 : fetch_word segs (at_ rb 0x50430) = Some W_50428.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 109 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5042c : fetch_word segs (at_ rb 0x50434) = Some W_5042c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 110 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50430 : fetch_word segs (at_ rb 0x50438) = Some W_50430.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 111 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50434 : fetch_word segs (at_ rb 0x5043c) = Some W_50434.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 112 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50438 : fetch_word segs (at_ rb 0x50440) = Some W_50438.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 113 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5043c : fetch_word segs (at_ rb 0x50444) = Some W_5043c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 114 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50440 : fetch_word segs (at_ rb 0x50448) = Some W_50440.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 115 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50444 : fetch_word segs (at_ rb 0x5044c) = Some W_50444.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 116 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50448 : fetch_word segs (at_ rb 0x50450) = Some W_50448.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 117 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5044c : fetch_word segs (at_ rb 0x50454) = Some W_5044c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 118 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50450 : fetch_word segs (at_ rb 0x50458) = Some W_50450.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 119 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50454 : fetch_word segs (at_ rb 0x5045c) = Some W_50454.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 120 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50458 : fetch_word segs (at_ rb 0x50460) = Some W_50458.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 121 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5045c : fetch_word segs (at_ rb 0x50464) = Some W_5045c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 122 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50460 : fetch_word segs (at_ rb 0x50468) = Some W_50460.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 123 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50464 : fetch_word segs (at_ rb 0x5046c) = Some W_50464.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 124 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50468 : fetch_word segs (at_ rb 0x50470) = Some W_50468.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 125 _ HCB eq_refl). Qed.


   (* [comment removed for export] *)
  Lemma J50478 : fetch_word segs (at_ rb 0x50480) = Some W_50478.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 129 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5047c : fetch_word segs (at_ rb 0x50484) = Some W_5047c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 130 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50480 : fetch_word segs (at_ rb 0x50488) = Some W_50480.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 131 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50484 : fetch_word segs (at_ rb 0x5048c) = Some W_50484.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 132 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50488 : fetch_word segs (at_ rb 0x50490) = Some W_50488.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 133 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5048c : fetch_word segs (at_ rb 0x50494) = Some W_5048c.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 134 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50490 : fetch_word segs (at_ rb 0x50498) = Some W_50490.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 135 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50494 : fetch_word segs (at_ rb 0x5049c) = Some W_50494.  Proof using HCB. exact (code_ato_get segs rb 0x5027c cb_words 136 _ HCB eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50504 : fetch_word segs (at_ rb 0x5050c) = Some W_50504.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 0 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50508 : fetch_word segs (at_ rb 0x50510) = Some W_50508.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 1 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5050c : fetch_word segs (at_ rb 0x50514) = Some W_5050c.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 2 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50510 : fetch_word segs (at_ rb 0x50518) = Some W_50510.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 3 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50514 : fetch_word segs (at_ rb 0x5051c) = Some W_50514.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 4 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50518 : fetch_word segs (at_ rb 0x50520) = Some W_50518.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 5 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5051c : fetch_word segs (at_ rb 0x50524) = Some W_5051c.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 6 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50520 : fetch_word segs (at_ rb 0x50528) = Some W_50520.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 7 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50524 : fetch_word segs (at_ rb 0x5052c) = Some W_50524.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 8 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50528 : fetch_word segs (at_ rb 0x50530) = Some W_50528.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 9 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J5052c : fetch_word segs (at_ rb 0x50534) = Some W_5052c.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 10 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50530 : fetch_word segs (at_ rb 0x50538) = Some W_50530.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 11 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50534 : fetch_word segs (at_ rb 0x5053c) = Some W_50534.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 12 _ HCBM eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J50538 : fetch_word segs (at_ rb 0x50540) = Some W_50538.  Proof using HCBM. exact (code_ato_get segs rb 0x5050c cbm_words 13 _ HCBM eq_refl). Qed.



   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache inst : word) (s : Z).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H10 : getr regs 10 = inst.
  Hypothesis H11 : getr regs 11 = cache.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 s.
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 8.
  Hypothesis Hs : (24 <= s <= 65536)%Z /\ (s mod 8 = 0)%Z.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-48)) 48 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.

  #[local] Abbreviation CLX := (fun r => In r (2 :: 8 :: cb_clob)).
  (* [comment removed for export] *)
  #[local] Abbreviation CLM := (fun r => In r (1 :: 9 :: 18 :: 19 :: 20 :: 2 :: 8 :: cbm_clob)).
  #[local] Abbreviation CLR := (fun r => In r (2 :: 8 :: cbm_clob)).

  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

  (* [comment removed for export] *)
  Lemma cbM : forall (M : word -> option byte) r0 (c : Z),
    getr r0 8 = Z_to_bv 64 c -> getr r0 2 = at_ sp (-48) -> getr r0 10 = inst -> getr r0 11 = cache -> getr r0 13 = Z_to_bv 64 8 ->
    regs_agree CLX regs r0 ->
    (1 <= c <= 30)%Z ->
    rdn segs M (at_ cache (80 * c)) 4 = Some (LE4 0) ->
    (U cache + 2584 <= U sp - 48)%Z ->
    exists r, msteps segs (mkst r0 (at_ rb 0x50410) M rom) (mkst r (at_ rb 0x509cc) M rom)
      /\ getr r 1 = at_ rb 0x5052c /\ getr r 2 = at_ sp (-48) /\ getr r 10 = cache /\ getr r 11 = at_ cache (80 * c) /\ getr r 12 = inst
      /\ getr r 13 = Z_to_bv 64 c /\ getr r 8 = Z_to_bv 64 c /\ getr r 9 = at_ cache (80 * c) /\ getr r 18 = Z_to_bv 64 8
      /\ getr r 19 = cache /\ getr r 20 = inst
      /\ regs_agree CLM regs r.
  Proof using G1 Hs s HCBM HCB.
    intros M r0 c R8 R2 R10 R11 R13 AG0 Hc Rcnt Gcs.
    destruct G1 as [G1a G1b]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache) as Hcr. pose proof (u64_range inst) as Hir.
    wd_eexists. split.
    - ab_ft J50408 D_50408 ltac:(condz).                  (* [comment removed for export] *)
      an J5040c D_5040c.                                   (* [comment removed for export] *)
      ab_ft J50410 D_50410 ltac:(condz).                  (* [comment removed for export] *)
      an J50414 D_50414.                                   (* [comment removed for export] *)
      av J50418 D_50418 (Z_to_bv 64 (80 * c)) ltac:(vz).  (* [comment removed for export] *)
      av J5041c D_5041c (at_ cache (80 * c)) ltac:(rewrite v_add_at by lia; reflexivity).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 0)) (v := Z_to_bv 64 0);
          [exact J50420 | reflexivity | exact D_50420 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; exact Rcnt | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small 0) by lia; vn.                 (* [comment removed for export] *)
      ab_tk J50424 D_50424 ltac:(condz).                  (* [comment removed for export] *)
      an J50504 D_50504.                                   (* [comment removed for export] *)
      an J50508 D_50508.                                   (* [comment removed for export] *)
      an J5050c D_5050c.                                   (* [comment removed for export] *)
      an J50510 D_50510.                                   (* [comment removed for export] *)
      an J50514 D_50514.                                   (* [comment removed for export] *)
      an J50518 D_50518.                                   (* [comment removed for export] *)
      an J5051c D_5051c.                                   (* [comment removed for export] *)
      an J50520 D_50520.                                   (* [comment removed for export] *)
      wd_refl.
    - post. unfold cbm_clob, cb_clob in *. ra_chain.
  Qed.



  (* [comment removed for export] *)
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis HGF : code_ato segs rb 0x50acc gf_words.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x50c74 0x50c84 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.
  Variables (nf : Z) (csz stw sbeg msk stv : word) (faf : Z -> Z).
  #[local] Abbreviation SPB := (U sbeg).
  #[local] Abbreviation cc := (class_of s).
  #[local] Abbreviation RIz := (U sbeg + 2 ^ 37 + 128 * class_of s)%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (U sbeg + 2 ^ 37 + 128 * class_of s)).
  #[local] Abbreviation FABz := (U sbeg + class_of s * 2 ^ 32 + 3758096384)%Z.
  Hypothesis HstkM : store_ok segs mem (at_ sp (-208)) 208 = true.        (* [comment removed for export] *)
  Hypothesis G1M : (U sbeg + 2 ^ 37 + 4096 + 208 <= U sp)%Z.
  Hypothesis GcM : (U cache + 2640 <= U sp - 208)%Z /\ (U cache mod 8 = 0)%Z.
  Hypothesis GcT : (U cache + 2640 <= U sbeg \/ U sbeg + 2 ^ 37 + 4096 <= U cache)%Z.
  Hypothesis GcI : (AIMGHI <= U cache \/ U cache + 2640 <= AIMGLO)%Z.
  Hypothesis Ginst : (AIMGLO <= U inst /\ U inst + 56 <= AIMGHI)%Z.
  Hypothesis GSPB : (U sbeg + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (U sbeg mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= U sbeg)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis Rcnt0 : rdn segs mem (at_ cache (80 * cc)) 4 = Some (LE4 0).
  Hypothesis Rcsz : rdn segs mem (at_ cache (80 * cc + 8)) 8 = Some (LE8 csz).
  Hypothesis Rstw : rdn segs mem (at_ cache 2576) 8 = Some (LE8 stw).
  Hypothesis SOKstw : store_ok segs mem (at_ cache 2576) 8 = true.
  Hypothesis SOKpc : store_ok segs mem (at_ cache (80 * cc)) 48 = true.
  Hypothesis Rsb : rdn segs mem (at_ inst 32) 8 = Some (LE8 sbeg).
  Hypothesis Rrib : rdn segs mem (at_ inst 48) 8 = Some (LE8 (Z_to_bv 64 (U sbeg + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis Hfaf : forall j, (Z.max 0 (nf - 8) <= j < nf)%Z -> rdn segs mem (Z_to_bv 64 (FABz + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.




  (* [comment removed for export] *)
  Lemma cb_miss_head :
    exists r3, msteps segs (mkst regs (at_ rb 0x5027c) mem rom) (mkst r3 (at_ rb 0x509cc) (cb_m1 regs mem ra sp) rom)
      /\ getr r3 1 = at_ rb 0x5052c /\ getr r3 2 = at_ sp (-48) /\ getr r3 10 = cache /\ getr r3 11 = at_ cache (80 * cc) /\ getr r3 12 = inst
      /\ getr r3 13 = Z_to_bv 64 cc /\ getr r3 8 = Z_to_bv 64 cc /\ getr r3 9 = at_ cache (80 * cc) /\ getr r3 18 = Z_to_bv 64 8
      /\ getr r3 19 = cache /\ getr r3 20 = inst /\ regs_agree CLM regs r3.
  Proof using G1 G1M GSPB GcI GcM GcT Ggm Ginst H1 H10 H11 H12 H13 H2 HCB HCBM Hnf Hs Hstk RB Rcnt0.
    destruct G1 as [G1a G1b]. destruct GcM as [Gc1 Gc2]. pose proof Hs as [Hs1 Hs2]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache).
    pose proof (AsArith3.class_of_range s ltac:(lia)) as Hc.
    destruct (cbP segs rb HCB regs mem rom ra sp cache inst s H1 H2 H10 H11 H12 H13 Hs Hstk G1) as (r1 & RUN1 & A2 & A10 & A11 & A12 & A13 & A14 & A15 & AG1).
    assert (CID : exists r2, msteps segs (mkst r1 (at_ rb 0x50300) (cb_m1 regs mem ra sp) rom) (mkst r2 (at_ rb 0x50410) (cb_m1 regs mem ra sp) rom)
              /\ getr r2 8 = Z_to_bv 64 cc /\ (forall i : reg, In i [2; 10; 11; 13] -> getr r2 i = getr r1 i) /\ regs_agree CLX regs r2).
    { destruct (Z.leb_spec s 512).
      - exact (cbLo segs rb HCB regs rom s Hs (cb_m1 regs mem ra sp) r1 ltac:(lia) A12 A14 AG1).
      - exact (cbHi segs rb HCB regs rom s Hs (cb_m1 regs mem ra sp) r1 ltac:(lia) A12 A14 AG1). }
    destruct CID as (r2 & RUN2 & B8 & BK & AG2).
    destruct (cbM (cb_m1 regs mem ra sp) r2 cc B8 ltac:(rewrite (BK 2) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A2) ltac:(rewrite (BK 10) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A10)
                ltac:(rewrite (BK 11) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A11) ltac:(rewrite (BK 13) by ((lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); solve [repeat (first [left; reflexivity | right])]); exact A13) AG2 Hc)
      as (r3 & RUN3 & C1 & C2 & C10 & C11 & C12 & C13 & C8 & C9 & C18 & C19 & C20 & AG3).
    { rewrite <- Rcnt0. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply (cb_m1_outside rb regs mem ra sp s G1); lia]. }
    { lia. }
    exists r3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    exact (conj C1 (conj C2 (conj C10 (conj C11 (conj C12 (conj C13 (conj C8 (conj C9 (conj C18 (conj C19 (conj C20 AG3))))))))))).
  Qed.


End CBM.
End FPGen1.
End AsAllocM3m.
Module AsAllocM3n.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM7r AsAllocM3m.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section AMBM.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL : code_ato segs rb 0x4bb24 al_words.
  Hypothesis HCB : code_ato segs rb 0x5027c cb_words.
  Hypothesis HCBM : code_ato segs rb 0x5050c cbm_words.
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis HGF : code_ato segs rb 0x50acc gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gt : gct_tab.
  Hypothesis GTOK : gct_tab_ok segs gt.
  Hypothesis GTRB : gt_rb gt = rb.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x50c74 0x50c84 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.

  Lemma J66cd8 : fetch_word segs (at_ rb 0x4bda4) = Some W_4bd9c.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 160 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J66cdc : fetch_word segs (at_ rb 0x4bda8) = Some W_4bda0.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 161 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J66ce0 : fetch_word segs (at_ rb 0x4bdac) = Some W_4bda4.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 162 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J66ce4 : fetch_word segs (at_ rb 0x4bdb0) = Some W_4bda8.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 163 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J66ce8 : fetch_word segs (at_ rb 0x4bdb4) = Some W_4bdac.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 164 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J66cec : fetch_word segs (at_ rb 0x4bdb8) = Some W_4bdb0.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 165 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J66cf0 : fetch_word segs (at_ rb 0x4bdbc) = Some W_4bdb4.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 166 _ HAL eq_refl). Qed.   (* [comment removed for export] *)
  Lemma J66cf4 : fetch_word segs (at_ rb 0x4bdc0) = Some W_4bdb8.  Proof using HAL. exact (code_ato_get segs rb 0x4bb24 al_words 167 _ HAL eq_refl). Qed.   (* [comment removed for export] *)

  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp tp tsdp tctx thr inst : word) (n : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (needed n).
  Hypothesis H22 : getr regs 22 = inst.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  Hypothesis GH : gctH segs gt mem sp tp tsdp tctx thr.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-208)) 208 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gthr : (4096 <= U thr /\ (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= U sp - 208)%Z /\ (U thr mod 8 = 0)%Z.
  Hypothesis Ginst : (AIMGLO <= U inst /\ U inst + 56 <= AIMGHI)%Z.
  (* [comment removed for export] *)
  Variables (nf : Z) (csz stw sbeg msk stv : word) (faf : Z -> Z).
  #[local] Abbreviation cc := (class_of (needed n)).
  #[local] Abbreviation RIz := (U sbeg + 2 ^ 37 + 128 * class_of (needed n))%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (U sbeg + 2 ^ 37 + 128 * class_of (needed n))).
  #[local] Abbreviation FABz := (U sbeg + class_of (needed n) * 2 ^ 32 + 3758096384)%Z.
  Hypothesis GTS : (U thr + 4096 <= U sbeg \/ U sbeg + 2 ^ 37 + 4096 <= U thr)%Z.
  Hypothesis G1M : (U sbeg + 2 ^ 37 + 4096 + 208 <= U sp)%Z.
  Hypothesis GSPB : (U sbeg + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (U sbeg mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= U sbeg)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis Rcnt0 : rdn segs mem (at_ thr (208 + 80 * cc)) 4 = Some (LE4 0).
  Hypothesis Rcsz : rdn segs mem (at_ thr (208 + 80 * cc + 8)) 8 = Some (LE8 csz).
  Hypothesis Rstw : rdn segs mem (at_ thr 2784) 8 = Some (LE8 stw).
  Hypothesis SOKstw : store_ok segs mem (at_ thr 2784) 8 = true.
  Hypothesis SOKpc : store_ok segs mem (at_ thr (208 + 80 * cc)) 48 = true.
  Hypothesis Rsb : rdn segs mem (at_ inst 32) 8 = Some (LE8 sbeg).
  Hypothesis Rrib : rdn segs mem (at_ inst 48) 8 = Some (LE8 (Z_to_bv 64 (U sbeg + 2 ^ 37))).
  Hypothesis Rmu : rdn segs mem RI 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis SOKmu : store_ok segs mem RI 8 = true.
  Hypothesis Rnf : rdn segs mem (at_ RI 16) 8 = Some (LE8 (Z_to_bv 64 nf)).
  Hypothesis SOKnf : store_ok segs mem (at_ RI 16) 8 = true.
  Hypothesis Rst : rdn segs mem (at_ RI 72) 8 = Some (LE8 stv).
  Hypothesis SOKst : store_ok segs mem (at_ RI 72) 8 = true.
  Hypothesis Rmsk : rdn segs mem (Z_to_bv 64 gmsk) 8 = Some (LE8 msk).
  Hypothesis Hfaf : forall j, (Z.max 0 (nf - 8) <= j < nf)%Z -> rdn segs mem (Z_to_bv 64 (FABz + 4 * j)) 4 = Some (LE4 (faf j)) /\ (0 <= faf j < 2 ^ 32)%Z.

  #[local] Abbreviation CLBm := (fun r => In r (26 :: 1 :: 5 :: 6 :: 7 :: 10 :: 11 :: 12 :: 13 :: 14 :: 15 :: 16 :: 17 :: 28 :: 29 :: 30 :: nil)).


  (* [comment removed for export] *)
  Ltac nixm Hx Hni Hnin := repeat (destruct Hx as [<-|Hx]; [first [apply Hni; solve [in_list] | apply Hnin; solve [in_list]] |]); destruct Hx.


  (* [comment removed for export] *)
  Lemma ambm_glue :
    exists r2 (M1 : word -> option byte),
      msteps segs (mkst regs (at_ rb 0x4bda4) mem rom) (mkst r2 (at_ rb 0x5027c) M1 rom)
      /\ M1 = wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4bda8))
      /\ getr r2 1 = at_ rb 0x4bdc4 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
      /\ getr r2 12 = Z_to_bv 64 (needed n) /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
      /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
      /\ (forall i : reg, ~ In i [26; 1; 10; 11; 12; 13] -> getr r2 i = getr regs i).
  Proof using sbeg Gthr G1 GH Hn H22 H19 H4 H2 tctx tsdp tp GTRB GTOK gt HAL.
    pose proof G1 as [G1a G1b]. pose proof Gthr as (Gt1 & Gt2 & Gt3). pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range inst) as Hir.
    pose proof (needed_facts n Hn) as NF. pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc.
    (* [comment removed for export] *)
    assert (W0 : exists r0, msteps segs (mkst regs (at_ rb 0x4bda4) mem rom) (mkst r0 (at_ rb 0x783bc) mem rom)
                 /\ getr r0 1 = at_ rb 0x4bda8 /\ (forall i : reg, i <> 1 -> getr r0 i = getr regs i)).
    { wd_eexists. split; [an J66cd8 D_4bd9c; wd_refl|]. split; [gres; reflexivity|]. intros i Hi. rewrite getr_other by (intros E; apply Hi; exact E). reflexivity. }
    destruct W0 as (r0 & RUN0 & A1 & AK).
    destruct (gct_run segs gt GTOK mem rom r0 (at_ rb 0x4bda8) sp tp tsdp tctx thr GH) as (r1 & RUN1 & B10 & B11 & AG1).
    { rewrite <- GTRB. pose proof (gto_rb _ _ GTOK) as [E1 E2]. pose proof (u64_range (gt_rb gt)). apply ret_ok_at; [exact E1 | reflexivity | lia]. }
    { exact A1. } { rewrite AK by (intros E; discriminate E). exact H2. } { rewrite AK by (intros E; discriminate E). exact H4. }
    rewrite GTRB in RUN1.
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4bda8))) in RUN1.
    (* [comment removed for export] *)
    Ltac r1eq AG1 AK r H := rewrite (AG1 r) by notin_list; rewrite (AK r) by (intros E; discriminate E); exact H.
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4bda8) M1 rom) (mkst r2 (at_ rb 0x5027c) M1 rom)
                 /\ getr r2 1 = at_ rb 0x4bdc4 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
                 /\ getr r2 12 = Z_to_bv 64 (needed n) /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
                 /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
                 /\ regs_agree (fun r => In r [26; 1; 10; 11; 12; 13]) r1 r2).
    { wd_eexists. split.
      - an J66cdc D_4bda0.                                   (* [comment removed for export] *)
        ab_ft J66ce0 D_4bda4 ltac:(condz).                  (* [comment removed for export] *)
        an J66ce4 D_4bda8.                                   (* [comment removed for export] *)
        an J66ce8 D_4bdac.                                   (* [comment removed for export] *)
        an J66cec D_4bdb0.                                   (* [comment removed for export] *)
        an J66cf0 D_4bdb4.                                   (* [comment removed for export] *)
        an J66cf4 D_4bdb8.                                   (* [comment removed for export] *)
        wd_refl.
      - post; rewrite ?B10, ?at_0; try reflexivity.
        + r1eq AG1 AK (2:reg) H2.
        + r1eq AG1 AK (22:reg) H22.
        + r1eq AG1 AK (19:reg) H19.
        + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; rewrite (AG1 _) by notin_list; apply AK; intros E; discriminate E|]); destruct Hi.
        + ra_solve. }
    destruct W2 as (r2 & RUN2 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AG2).
    exists r2, M1. split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [reflexivity|]. split; [exact C1|]. split; [exact C2|]. split; [exact C10|]. split; [exact C11|]. split; [exact C12|]. split; [exact C13|]. split; [exact C26|].
    split; [exact CK|].
    intros i Hni. rewrite (AG2 i Hni). rewrite (AG1 i); [apply AK; intros ->; apply Hni; solve [in_list]|].
    intros Hx. cbn [gct_clob In] in Hx. repeat (destruct Hx as [<-|Hx]; [apply Hni; solve [in_list]|]). destruct Hx.
  Qed.


End AMBM.
End FPGen1.
End AsAllocM3n.
Module AsAllocM3p.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM7r AsAllocM3m AsAllocM3n.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition amh_M1 (rb : word) (mem : word -> option byte) (sp : word) : word -> option byte := wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4bda8)).
Definition amh_mem (rb : word) (regs : bvmap 5 word) (mem : word -> option byte) (sp : word) : word -> option byte :=
  cb_m1 regs (amh_M1 rb mem sp) (at_ rb 0x4bdc4) sp.
Lemma amh_M1_outside : forall rb mem (sp : word), (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z ->
  forall x : word, (U x < U sp - 8 \/ U sp <= U x)%Z -> amh_M1 rb mem sp x = mem x.
Proof using.
  intros rb mem sp [G1a G1b] x Hx. pose proof (u64_range sp). (lazymatch goal with |- ?G => let G' := eval unfold amh_M1 in G in change_no_check G' end).
  rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.
Lemma amh_mem_outside : forall rb regs mem (sp : word), (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z ->
  forall x : word, (U x < U sp - 48 \/ U sp <= U x)%Z -> amh_mem rb regs mem sp x = mem x.
Proof using.
  intros rb regs mem sp G1 x Hx. (lazymatch goal with |- ?G => let G' := eval unfold amh_mem in G in change_no_check G' end). rewrite (cb_m1_outside rb regs (amh_M1 rb mem sp) (at_ rb 0x4bdc4) sp 24 G1) by exact Hx.
  apply amh_M1_outside; [exact G1 | lia].
Qed.
Lemma amh_mem_grows : forall rb regs mem sp, mem_grows mem (amh_mem rb regs mem sp).
Proof using. intros rb regs mem sp. (lazymatch goal with |- ?G => let G' := eval unfold amh_mem in G in change_no_check G' end). eapply mem_grows_trans; [(lazymatch goal with |- ?G => let G' := eval unfold amh_M1 in G in change_no_check G' end); apply wbytes_grows | apply cb_m1_grows]. Qed.
(* [comment removed for export] *)
Lemma amh_mem_slots : forall segs rb regs mem (sp : word), (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z ->
  forall (k : Z) (v : word), In (k, v) [(-8, at_ rb 0x4bdc4); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20)]%Z ->
  rdn segs (amh_mem rb regs mem sp) (at_ sp k) 8 = Some (LE8 v).
Proof using. intros segs rb regs mem sp G1 k v Hin. (lazymatch goal with |- ?G => let G' := eval unfold amh_mem in G in change_no_check G' end). exact (cb_m1_slots segs rb regs (amh_M1 rb mem sp) (at_ rb 0x4bdc4) sp 24 G1 k v Hin). Qed.

Section AMBM.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL : code_ato segs rb 0x4bb24 al_words.
  Hypothesis HCB : code_ato segs rb 0x5027c cb_words.
  Hypothesis HCBM : code_ato segs rb 0x5050c cbm_words.
  Hypothesis HRF : code_ato segs rb 0x509cc rf_words.
  Hypothesis HGF : code_ato segs rb 0x50acc gf_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gt : gct_tab.
  Hypothesis GTOK : gct_tab_ok segs gt.
  Hypothesis GTRB : gt_rb gt = rb.
  Variable gmsk : Z.
  Hypothesis GMSK : gauipc_ld segs rb 0x50c74 0x50c84 14 14 gmsk.
  Hypothesis Ggm : (AIMGLO <= gmsk /\ gmsk + 8 <= AIMGHI)%Z.


  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp tp tsdp tctx thr inst : word) (n : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 (needed n).
  Hypothesis H22 : getr regs 22 = inst.
  Hypothesis Hn : (1 <= n <= 64512)%Z.
  Hypothesis GH : gctH segs gt mem sp tp tsdp tctx thr.
  Hypothesis Hstk : store_ok segs mem (at_ sp (-208)) 208 = true.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gthr : (4096 <= U thr /\ (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= U sp - 208)%Z /\ (U thr mod 8 = 0)%Z.
  Hypothesis Ginst : (AIMGLO <= U inst /\ U inst + 56 <= AIMGHI)%Z.

  Variables (nf : Z) (sbeg : word).
  #[local] Abbreviation cc := (class_of (needed n)).
  Hypothesis GTS : (U thr + 4096 <= U sbeg \/ U sbeg + 2 ^ 37 + 4096 <= U thr)%Z.
  Hypothesis G1M : (U sbeg + 2 ^ 37 + 4096 + 208 <= U sp)%Z.
  Hypothesis GSPB : (U sbeg + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (U sbeg mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= U sbeg)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  Hypothesis Rcnt0 : rdn segs mem (at_ thr (208 + 80 * cc)) 4 = Some (LE4 0).

  Theorem amB_miss_head :
    exists r3, msteps segs (mkst regs (at_ rb 0x4bda4) mem rom) (mkst r3 (at_ rb 0x509cc) (amh_mem rb regs mem sp) rom)
      /\ getr r3 1 = at_ rb 0x5052c /\ getr r3 2 = at_ sp (-48) /\ getr r3 10 = at_ thr 208 /\ getr r3 11 = at_ thr (208 + 80 * cc) /\ getr r3 12 = inst
      /\ getr r3 13 = Z_to_bv 64 cc /\ getr r3 8 = Z_to_bv 64 cc /\ getr r3 9 = at_ thr (208 + 80 * cc) /\ getr r3 18 = Z_to_bv 64 8
      /\ getr r3 19 = at_ thr 208 /\ getr r3 20 = inst /\ getr r3 26 = thr
      /\ (forall i : reg, In i [3; 4; 21; 22; 23; 24; 25; 27] -> getr r3 i = getr regs i).
  Proof using Rcnt0 Hnf GSPB G1M GTS sbeg nf Ginst Gthr G1 Hstk GH Hn H22 H19 H4 H2 tctx tsdp tp Ggm gmsk GTRB GTOK gt RB HCBM HCB HAL.
    pose proof G1 as [G1a G1b]. pose proof Gthr as (Gt1 & Gt2 & Gt3). destruct GSPB as (S2 & S3 & S4). destruct Ginst as [Gi1 Gi2].
    pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range inst) as Hir. pose proof (u64_range sbeg).
    pose proof (needed_facts n Hn) as NF. pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc.
    destruct (ambm_glue segs rb HAL gt GTOK GTRB regs mem rom sp tp tsdp tctx thr inst n H2 H4 H19 H22 Hn GH G1 Gthr sbeg)
      as (r2 & M1 & RUN12 & EM1 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AGK).
    assert (EM : M1 = amh_M1 rb mem sp) by exact EM1.
    assert (GRM1 : mem_grows mem M1) by (rewrite EM1; apply wbytes_grows).
    destruct (cb_miss_head segs rb HCB HCBM RB r2 M1 rom (at_ rb 0x4bdc4) sp (at_ thr 208) inst (needed n)
                C1 C2 C10 C11 C12 C13 NF
                ltac:(eapply store_ok_mono; [exact GRM1|]; eapply (store_ok_sub segs mem (at_ sp (-208)) _ 208); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia])
                G1 gmsk Ggm nf sbeg G1M
                ltac:(rewrite at_u by lia; split; [lia | rewrite <- Zplus_mod_idemp_l, Gt3; reflexivity])
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) (conj Gi1 Gi2) (conj S2 (conj S3 S4)) Hnf)
      as (r3 & RUN3 & D1 & D2 & D10 & D11 & D12 & D13 & D8 & D9 & D18 & D19 & D20 & AG3).
    { rewrite at_at. rewrite <- Rcnt0. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ]|]. intros x Hx. rewrite at_u in Hx by lia. cbn in Hx.
      rewrite EM. apply (amh_M1_outside rb mem sp G1). lia. }
    assert (EMEM : cb_m1 r2 M1 (at_ rb 0x4bdc4) sp = amh_mem rb regs mem sp).
    { (lazymatch goal with |- ?G => let G' := eval unfold amh_mem, cb_m1 in G in change_no_check G' end). rewrite EM. rewrite !(CK _) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20). reflexivity. }
    rewrite EMEM in RUN3. rewrite !at_at in D11, D9.
    exists r3. split; [eapply msteps_trans; [exact RUN12 | exact RUN3]|].
    split; [exact D1|]. split; [exact D2|]. split; [exact D10|]. split; [exact D11|]. split; [exact D12|]. split; [exact D13|]. split; [exact D8|].
    split; [exact D9|]. split; [exact D18|]. split; [exact D19|]. split; [exact D20|]. split.
    - rewrite (AG3 26) by notin. exact C26.
    - intros i Hi. rewrite (AG3 i); [apply CK; cbn [In] in Hi |- *; clear - Hi; tauto|].
      cbn [In] in Hi. intros Hx. unfold cbm_clob in Hx. cbn [In] in Hx.
      repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi.
  Qed.
End AMBM.
End FPGen1.
End AsAllocM3p.
Module AsAllocM3q.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM7r AsAllocM3m.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac wd_setR ::= wd_setR_on.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.
Section CBM2.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HCB : code_ato segs rb 0x5027c cb_words.
  Hypothesis HCBM : code_ato segs rb 0x5050c cbm_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Let K50428 := J50428 segs rb HCB.
  Let K5042c := J5042c segs rb HCB.
  Let K50430 := J50430 segs rb HCB.
  Let K50434 := J50434 segs rb HCB.
  Let K50438 := J50438 segs rb HCB.
  Let K5043c := J5043c segs rb HCB.
  Let K50440 := J50440 segs rb HCB.
  Let K50444 := J50444 segs rb HCB.
  Let K50448 := J50448 segs rb HCB.
  Let K5044c := J5044c segs rb HCB.
  Let K50450 := J50450 segs rb HCB.
  Let K50454 := J50454 segs rb HCB.
  Let K50458 := J50458 segs rb HCB.
  Let K5045c := J5045c segs rb HCB.
  Let K50460 := J50460 segs rb HCB.
  Let K50464 := J50464 segs rb HCB.
  Let K50468 := J50468 segs rb HCB.
  Let K50478 := J50478 segs rb HCB.
  Let K5047c := J5047c segs rb HCB.
  Let K50480 := J50480 segs rb HCB.
  Let K50484 := J50484 segs rb HCB.
  Let K50488 := J50488 segs rb HCB.
  Let K5048c := J5048c segs rb HCB.
  Let K50490 := J50490 segs rb HCB.
  Let K50494 := J50494 segs rb HCB.
  Let K50524 := J50524 segs rb HCBM.
  Let K50528 := J50528 segs rb HCBM.
  Let K5052c := J5052c segs rb HCBM.
  Let K50530 := J50530 segs rb HCBM.
  Let K50534 := J50534 segs rb HCBM.
  Let K50538 := J50538 segs rb HCBM.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ra sp cache inst : word).
  Hypothesis Hret : ret_ok ra.
  Hypothesis H1 : getr regs 1 = ra.
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Definition cb_slots2 : list (Z * word) := [(-8, ra); (-16, getr regs 8); (-24, getr regs 9); (-32, getr regs 18); (-40, getr regs 19); (-48, getr regs 20)]%Z.

  Ltac vz := cbv delta [v_add v_addi v_mul v_slli v_srli v_sub] beta; rewrite ?Z.shiftl_mul_pow2, ?Z.shiftr_div_pow2 by lia; unorm;
             first [reflexivity | f_equal; lia | apply bv_eq; wd_ulia].

  Lemma cbR2 : forall (M : word -> option byte) r0 (c cnt k : Z) (csz stw sbeg res : word),
    getr r0 8 = Z_to_bv 64 c -> getr r0 2 = at_ sp (-48) -> getr r0 9 = at_ cache (80 * c) -> getr r0 18 = Z_to_bv 64 8 ->
    getr r0 19 = cache -> getr r0 20 = inst -> getr r0 10 = res -> U res <> 0%Z ->
    (1 <= c <= 30)%Z -> (1 <= cnt <= 16)%Z -> (0 <= k < 2 ^ 32)%Z ->
    rdn segs M (at_ cache (80 * c)) 4 = Some (LE4 cnt) ->
    rdn segs M (at_ cache (80 * c + 8)) 8 = Some (LE8 csz) ->
    rdn segs M (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k) ->
    rdn segs M (at_ cache 2576) 8 = Some (LE8 stw) ->
    store_ok segs M (at_ cache (80 * c)) 4 = true -> store_ok segs M (at_ cache 2576) 8 = true ->
    rdn segs M (at_ inst 32) 8 = Some (LE8 sbeg) ->
    (forall (o : Z) (v : word), In (o, v) cb_slots2 -> rdn segs M (at_ sp o) 8 = Some (LE8 v)) ->
    (U cache mod 8 = 0)%Z -> (U inst + 40 <= U cache \/ U cache + 2584 <= U inst)%Z -> (U cache + 2584 <= U sp - 48)%Z -> (U inst + 40 <= 2 ^ 32)%Z ->
    (U sbeg + 2 ^ 37 < 2 ^ 64)%Z ->
    let M1 := wbytes M (at_ cache (80 * c)) (LE4 (cnt - 1)) in
    let M' := wbytes M1 (at_ cache 2576) (LE8 (v_add stw csz)) in
    exists r, msteps segs (mkst r0 (at_ rb 0x5052c) M rom) (mkst r ra M' rom)
      /\ getr r 10 = Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)
      /\ getr r 13 = Z_to_bv 64 8
      /\ (forall i : reg, In i [1; 2; 8; 9; 18; 19; 20] -> getr r i = getr regs i)
      /\ (forall i : reg, In i [3; 4; 21; 22; 23; 24; 25; 26; 27] -> getr r i = getr r0 i).
  Proof using G1 H2 H1 Hret mem K50538 K50534 K50530 K5052c K50528 K50524 K50494 K50490 K5048c K50488 K50484 K50480 K5047c K50478 K50468 K50464 K50460 K5045c K50458 K50454 K50450 K5044c K50448 K50444 K50440 K5043c K50438 K50434 K50430 K5042c K50428 RB HCBM HCB.
    intros M r0 c cnt k csz stw sbeg res R8 R2 R9 R18 R19 R20 R10 NZ Hc Hcnt Hk Rcnt Rcsz Rk Rst SOKc SOKs Rsb FR AL8 Gc Gcs Gi Gsb M1 M'.
    pose proof (u64_range res) as Hres.
    destruct G1 as [G1a G1b]. pose proof (u64_range sp) as Hspr. pose proof (u64_range cache) as Hcr. pose proof (u64_range inst) as Hir.
    pose proof (u64_range sbeg) as Hsbr.
    assert (M1_out : forall x : word, (U x < U cache + 80 * c \/ U cache + 80 * c + 4 <= U x)%Z -> M1 x = M x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [reflexivity | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (M'_out : forall x : word, (U x < U cache + 80 * c \/ U cache + 80 * c + 4 <= U x)%Z -> (U x < U cache + 2576 \/ U cache + 2584 <= U x)%Z -> M' x = M x).
    { intros x Hx Hy. (lazymatch goal with |- ?G => let G' := eval unfold M' in G in change_no_check G' end). rewrite wbytes_outside; [apply M1_out; exact Hx | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    assert (Rcsz1 : rdn segs M1 (at_ cache (80 * c + 8)) 8 = Some (LE8 csz)).
    { rewrite <- Rcsz. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Rk1 : rdn segs M1 (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k)).
    { rewrite <- Rk. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (Rst1 : rdn segs M1 (at_ cache 2576) 8 = Some (LE8 stw)).
    { rewrite <- Rst. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; apply M1_out; rewrite at_u in Hx by lia; cbn in Hx; lia]. }
    assert (SOKs1 : store_ok segs M1 (at_ cache 2576) 8 = true).
    { (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). eapply store_ok_mono; [apply wbytes_grows | exact SOKs]. }
    assert (Rsb' : rdn segs M' (at_ inst 32) 8 = Some (LE8 sbeg)).
    { rewrite <- Rsb. apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply M'_out; lia]. }
    assert (FR' : forall (o : Z) (v : word), In (o, v) cb_slots2 -> rdn segs M' (at_ sp o) 8 = Some (LE8 v)).
    { intros o v Hin. rewrite <- (FR o v Hin).
      assert (Ho : (-48 <= o <= -8)%Z). { cbn [In cb_slots2] in Hin. repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). destruct Hin. }
      apply rdn_ext; [first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); wd_zofnat; lia ] | rewrite at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia ] | intros x Hx; rewrite at_u in Hx by lia; cbn in Hx; apply M'_out; lia]. }
    wd_eexists. split; [|split; [|split; [|split]]].
    - ab_ft K50524 D_50524 ltac:(condz).                  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lw with (bs := word_to_le_bytes 4 (Z_to_bv 64 cnt)) (v := Z_to_bv 64 cnt);
          [exact K50528 | reflexivity | exact D_50528 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; exact Rcnt | apply bytes4_small; lia]
        | step_simpl]; rewrite (v_lw_small cnt) by lia; vn.                 (* [comment removed for export] *)
      an K5052c D_5052c.                                   (* [comment removed for export] *)
      an K50530 D_50530.                                   (* [comment removed for export] *)
      an K50534 D_50534.                                   (* [comment removed for export] *)
      an K50538 D_50538.                                   (* [comment removed for export] *)
      av K50428 D_50428 (Z_to_bv 64 (cnt - 1)) ltac:(vz). (* [comment removed for export] *)
      an K5042c D_5042c.                                   (* [comment removed for export] *)
      av K50430 D_50430 (Z_to_bv 64 ((cnt - 1) * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_sw_at with (a := at_ cache (80 * c));
          [exact K50434 | reflexivity | exact D_50434
          | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_add_0_r; reflexivity
          | gres; rwH; reflexivity
          | exact SOKc ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M _ _) with M1.
      an K50438 D_50438.                                   (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 csz) (v := csz);
          [exact K5043c | reflexivity | exact D_5043c | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rcsz1 | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K50440 D_50440 (Z_to_bv 64 (4 * (cnt - 1))) ltac:(cbv delta [v_srli] beta; rewrite Z.shiftr_div_pow2 by lia; unorm; f_equal;
            replace ((cnt - 1) * 2 ^ 32)%Z with (4 * (cnt - 1) * 2 ^ 30)%Z by lia; apply Z.div_mul; lia).   (* [comment removed for export] *)
      av K50444 D_50444 (at_ cache (80 * c + 4 * (cnt - 1))) ltac:(rewrite v_add_at by lia; rewrite at_at; first [reflexivity | f_equal; lia]).  (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_lwu with (bs := word_to_le_bytes 4 (Z_to_bv 64 k)) (v := Z_to_bv 64 k);
          [exact K50448 | reflexivity | exact D_50448
          | gres; rwH; imm_norm; rewrite ?at_addi; zlit_at; rewrite <- Rk1; f_equal; f_equal; lia
          | apply bytes4_small; lia]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      chain_step; [reflexivity
        | eapply step_amoadd_d with (bs := LE8 stw) (v := stw);
          [exact K5044c | reflexivity | exact D_5044c
          | gres; rwH; rewrite at_u by lia; rewrite <- Zplus_mod_idemp_l, AL8; reflexivity
          | gres; rwH; exact Rst1
          | apply bytes_le_to_Z_8
          | gres; rwH; exact SOKs1 ]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      change (wbytes M1 _ _) with M'.
      chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 sbeg) (v := sbeg);
          [exact K50450 | reflexivity | exact D_50450 | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi; zlit_at; exact Rsb' | apply bytes_le_to_Z_8]
        | step_simpl]; vn.                                 (* [comment removed for export] *)
      av K50454 D_50454 (Z_to_bv 64 (c * 2 ^ 32)) ltac:(vz).        (* [comment removed for export] *)
      av K50458 D_50458 (Z_to_bv 64 (16 * k)) ltac:(vz).            (* [comment removed for export] *)
      av K5045c D_5045c (Z_to_bv 64 (U sbeg + c * 2 ^ 32)) ltac:(vz).   (* [comment removed for export] *)
      av K50460 D_50460 (Z_to_bv 64 (U sbeg + c * 2 ^ 32 + 16 * k)) ltac:(vz).   (* [comment removed for export] *)
      an K50464 D_50464.                                   (* [comment removed for export] *)
      ab_tk K50468 D_50468 ltac:(condz).                  (* [comment removed for export] *)
      Ltac cldF F D vv H := chain_step; [reflexivity
        | eapply step_ld with (bs := LE8 vv) (v := vv);
          [exact F | reflexivity | exact D | gres; rwH; imm_norm; rewrite ?v_addi_0, ?at_addi, ?at_at; zlit_at; apply H; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); tauto | apply bytes_le_to_Z_8]
        | step_simpl]; vn.
      cldF K50478 D_50478 ra (FR' (-8)%Z).                        (* [comment removed for export] *)
      cldF K5047c D_5047c (getr regs 8) (FR' (-16)%Z).             (* [comment removed for export] *)
      cldF K50480 D_50480 (getr regs 9) (FR' (-24)%Z).             (* [comment removed for export] *)
      cldF K50484 D_50484 (getr regs 18) (FR' (-32)%Z).            (* [comment removed for export] *)
      cldF K50488 D_50488 (getr regs 19) (FR' (-40)%Z).            (* [comment removed for export] *)
      cldF K5048c D_5048c (getr regs 20) (FR' (-48)%Z).            (* [comment removed for export] *)
      an K50490 D_50490.                                   (* [comment removed for export] *)
      aret K50494 D_50494 ra.                              (* [comment removed for export] *)
      wd_refl.
    - gres. reflexivity.
    - gres. rwH. reflexivity.
    - intros i Hi; cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [gres; rwH; rewrite ?at_0; first [reflexivity | symmetry; assumption] |]). destruct Hi.
    - intros i Hi; cbn [In] in Hi.
      repeat (destruct Hi as [<-|Hi]; [gres; reflexivity |]). destruct Hi.
  Qed.
End CBM2.
End FPGen1.
End AsAllocM3q.
Module AsAllocM9e.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.WalkLetEv.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib.AsRtAtomic OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac.AsCodeM0 OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM7r AsAllocM3m.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation U := bv_unsigned.

Section FPGen1.
Context {fx : FPState}.

Section AMBS.
  Variable segs : list Segment.
  Variable rb : word.
  Hypothesis HAL : code_ato segs rb 0x4bb24 al_words.
  Hypothesis RB : (U rb mod 2 = 0)%Z /\ (U rb + 2 ^ 24 < 2 ^ 64)%Z.
  Variable gt : gct_tab.
  Hypothesis GTOK : gct_tab_ok segs gt.
  Hypothesis GTRB : gt_rb gt = rb.
  Variables (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (sp tp tsdp tctx thr inst : word) (sz : Z).
  Hypothesis H2 : getr regs 2 = sp.
  Hypothesis H4 : getr regs 4 = tp.
  Hypothesis H19 : getr regs 19 = Z_to_bv 64 sz.
  Hypothesis H22 : getr regs 22 = inst.
  Hypothesis GH : gctH segs gt mem sp tp tsdp tctx thr.
  Hypothesis G1 : (2 ^ 32 + 48 <= U sp)%Z /\ (U sp + 16 <= 2 ^ 47)%Z.
  Hypothesis Gthr : (4096 <= U thr /\ (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr))%Z /\ (U thr + 4096 <= U sp - 208)%Z /\ (U thr mod 8 = 0)%Z.
  Let J66cd8 := AsAllocM3.J66cd8 segs rb HAL.
  Let J66cdc := AsAllocM3.J66cdc segs rb HAL.
  Let J66ce0 := AsAllocM3.J66ce0 segs rb HAL.
  Let J66ce4 := AsAllocM3.J66ce4 segs rb HAL.
  Let J66ce8 := AsAllocM3.J66ce8 segs rb HAL.
  Let J66cec := AsAllocM3.J66cec segs rb HAL.
  Let J66cf0 := AsAllocM3.J66cf0 segs rb HAL.
  Let J66cf4 := AsAllocM3.J66cf4 segs rb HAL.

  Lemma ambs_glue :
    exists r2 (M1 : word -> option byte),
      msteps segs (mkst regs (at_ rb 0x4bda4) mem rom) (mkst r2 (at_ rb 0x5027c) M1 rom)
      /\ M1 = wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4bda8))
      /\ getr r2 1 = at_ rb 0x4bdc4 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
      /\ getr r2 12 = Z_to_bv 64 sz /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
      /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
      /\ (forall i : reg, ~ In i [26; 1; 10; 11; 12; 13] -> getr r2 i = getr regs i).
  Proof using J66cf4 J66cf0 J66cec J66ce8 J66ce4 J66ce0 J66cdc J66cd8 Gthr G1 GH H22 H19 H4 H2 tctx tsdp tp GTRB GTOK gt HAL.
    pose proof G1 as [G1a G1b]. pose proof Gthr as (Gt1 & Gt2 & Gt3). pose proof (u64_range sp) as Hspr. pose proof (u64_range thr) as Hthr. pose proof (u64_range inst) as Hir.
    (* [comment removed for export] *)
    assert (W0 : exists r0, msteps segs (mkst regs (at_ rb 0x4bda4) mem rom) (mkst r0 (at_ rb 0x783bc) mem rom)
                 /\ getr r0 1 = at_ rb 0x4bda8 /\ (forall i : reg, i <> 1 -> getr r0 i = getr regs i)).
    { wd_eexists. split; [an J66cd8 D_4bd9c; wd_refl|]. split; [gres; reflexivity|]. intros i Hi. rewrite getr_other by (intros E; apply Hi; exact E). reflexivity. }
    destruct W0 as (r0 & RUN0 & A1 & AK).
    destruct (gct_run segs gt GTOK mem rom r0 (at_ rb 0x4bda8) sp tp tsdp tctx thr GH) as (r1 & RUN1 & B10 & B11 & AG1).
    { rewrite <- GTRB. pose proof (gto_rb _ _ GTOK) as [E1 E2]. pose proof (u64_range (gt_rb gt)). apply ret_ok_at; [exact E1 | reflexivity | lia]. }
    { exact A1. } { rewrite AK by (intros E; discriminate E). exact H2. } { rewrite AK by (intros E; discriminate E). exact H4. }
    rewrite GTRB in RUN1.
    set (M1 := wbytes mem (at_ sp (-8)) (LE8 (at_ rb 0x4bda8))) in RUN1.
    (* [comment removed for export] *)
    Ltac r1eq AG1 AK r H := rewrite (AG1 r) by notin_list; rewrite (AK r) by (intros E; discriminate E); exact H.
    assert (W2 : exists r2, msteps segs (mkst r1 (at_ rb 0x4bda8) M1 rom) (mkst r2 (at_ rb 0x5027c) M1 rom)
                 /\ getr r2 1 = at_ rb 0x4bdc4 /\ getr r2 2 = sp /\ getr r2 10 = inst /\ getr r2 11 = at_ thr 208
                 /\ getr r2 12 = Z_to_bv 64 sz /\ getr r2 13 = Z_to_bv 64 8 /\ getr r2 26 = thr
                 /\ (forall i : reg, In i [4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 27; 3] -> getr r2 i = getr regs i)
                 /\ regs_agree (fun r => In r [26; 1; 10; 11; 12; 13]) r1 r2).
    { wd_eexists. split.
      - an J66cdc D_4bda0.                                   (* [comment removed for export] *)
        ab_ft J66ce0 D_4bda4 ltac:(condz).                  (* [comment removed for export] *)
        an J66ce4 D_4bda8.                                   (* [comment removed for export] *)
        an J66ce8 D_4bdac.                                   (* [comment removed for export] *)
        an J66cec D_4bdb0.                                   (* [comment removed for export] *)
        an J66cf0 D_4bdb4.                                   (* [comment removed for export] *)
        an J66cf4 D_4bdb8.                                   (* [comment removed for export] *)
        wd_refl.
      - post; rewrite ?B10, ?at_0; try reflexivity.
        + r1eq AG1 AK (2:reg) H2.
        + r1eq AG1 AK (22:reg) H22.
        + r1eq AG1 AK (19:reg) H19.
        + intros i Hi; cbn [In] in Hi; repeat (destruct Hi as [<-|Hi]; [gres; rewrite (AG1 _) by notin_list; apply AK; intros E; discriminate E|]); destruct Hi.
        + ra_solve. }
    destruct W2 as (r2 & RUN2 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AG2).
    exists r2, M1. split; [eapply msteps_trans; [exact RUN0|]; eapply msteps_trans; [exact RUN1 | exact RUN2]|].
    split; [reflexivity|]. split; [exact C1|]. split; [exact C2|]. split; [exact C10|]. split; [exact C11|]. split; [exact C12|]. split; [exact C13|]. split; [exact C26|].
    split; [exact CK|].
    intros i Hni. rewrite (AG2 i Hni). rewrite (AG1 i); [apply AK; intros ->; apply Hni; solve [in_list]|].
    intros Hx. cbn [gct_clob In] in Hx. repeat (destruct Hx as [<-|Hx]; [apply Hni; solve [in_list]|]). destruct Hx.
  Qed.

End AMBS.
End FPGen1.
End AsAllocM9e.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.glaze.binary_reflection.images.Asan.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMIm.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.As_code_50024_51024 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM3m OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Section FPGen.
Context {fx : FPState}.

Lemma asan_HCBM : code_ato ASEGS ARB 0x5050c cbm_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold cbm_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_HRF : code_ato ASEGS ARB 0x509cc rf_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold rf_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_HGF : code_ato ASEGS ARB 0x50acc gf_words.
Proof using. (lazymatch goal with |- ?G => let G' := eval unfold gf_words in G in change_no_check G' end). code_ato_vm. Qed.
Lemma asan_GMSK : gauipc_ld ASEGS ARB 0x50c74 0x50c84 14 14 0x10470.
Proof using. gauipc_ld_tac F_50c6c D_50c6c F_50c7c D_50c7c. Qed.

(* [comment removed for export] *)
Lemma rdn_rom_total : forall (M : word -> option byte) (a : word) (n : nat),
  (bv_unsigned a + Z.of_nat n < 2 ^ 64)%Z ->
  (forall i : Z, (bv_unsigned a <= i < bv_unsigned a + Z.of_nat n)%Z -> seg_rom ASEGS (Z_to_bv 64 i) <> None) ->
  exists bs, rdn ASEGS M a n = Some bs /\ length bs = n.
Proof using.
  intros M a n; revert a; induction n as [|n IH]; intros a Hn ROM.
  - exists []%list. split; reflexivity.
  - pose proof (u64_range a) as Ha. (lazymatch goal with |- ?G => let G' := eval cbn [rdn] in G in change_no_check G' end).
    assert (B : exists b, match M a with Some b => Some b | None => seg_rom ASEGS a end = Some b).
    { destruct (M a) as [b|]; [exists b; reflexivity|].
      destruct (seg_rom ASEGS a) as [b|] eqn:E; [exists b; reflexivity|]. exfalso. apply (ROM (bv_unsigned a) ltac:(lia)). rewrite Z_to_bv_bv_unsigned. exact E. }
    destruct B as [b Eb]. rewrite Eb.
    destruct (IH (a + 1)%bv) as (bs & R & L).
    + rewrite u_add1 by lia. lia.
    + intros i Hi. apply ROM. rewrite u_add1 in Hi by lia. lia.
    + rewrite R. exists (b :: bs)%list. split; [reflexivity | (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
Qed.

Lemma rom_10470 : forall i : Z, (0x10470 <= i < 0x10470 + 8)%Z -> seg_rom ASEGS (Z_to_bv 64 i) <> None.
Proof using.
  intros i Hi.
  assert (C : (i = 0x10470 \/ i = 0x10471 \/ i = 0x10472 \/ i = 0x10473 \/ i = 0x10474 \/ i = 0x10475 \/ i = 0x10476 \/ i = 0x10477)%Z) by lia.
  destruct C as [->|[->|[->|[->|[->|[->|[->| ->]]]]]]]; vm_compute; discriminate.
Qed.

Lemma asan_mask_rdn : forall M : word -> option byte, exists msk : word, rdn ASEGS M (Z_to_bv 64 0x10470) 8 = Some (word_to_le_bytes 8 msk).
Proof using.
  intros M. destruct (rdn_rom_total M (Z_to_bv 64 0x10470) 8 ltac:(wd_ulia_c) ltac:(unorm; exact rom_10470)) as (bs & R & L).
  exists (Z_to_bv 64 (bytes_le_to_Z bs)). rewrite R. rewrite (word_to_le_bytes_of_bytes8 bs L). reflexivity.
Qed.
End FPGen.
End AsAllocMIm.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module AsAllocMRunP.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM3m AsAllocM3n AsAllocM3p AsAllocM3q AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.AsAllocMTag.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Ltac wm_parts H :=
  let T := type of H in
  lazymatch T with
  | ?A /\ ?B => let H1 := fresh "wmp" in let H2 := fresh "wmp" in
                pose proof (proj1 H) as H1; pose proof (proj2 H) as H2; wm_parts H1; wm_parts H2;
                (lazymatch A with context [or] => clear H1 | _ => idtac end);
                (lazymatch B with context [or] => lazymatch B with _ /\ _ => clear H2 | _ => idtac end | _ => idtac end)
  | _ => idtac
  end.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit. exact Hc. Qed.

(* [comment removed for export] *)
Ltac notin' := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin.
Ltac rch := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notin' end end ]).

(* [comment removed for export] *)
Lemma rdn1_off : forall (m : mem) (a : word) b,
  (bv_unsigned a + 1 <= 0x10000 \/ 0x65d000 <= bv_unsigned a)%Z -> rdn ASEGS m a 1 = Some [b] -> m a = Some b.
Proof using.
  intros m a b Ha R. cbn [rdn] in R. destruct (m a) as [b'|] eqn:E.
  - cbn in R. congruence.
  - unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1%Z in R.
    rewrite (find_segment1_none_outside ASEGS 0x10000 0x65d000 (bv_unsigned a) asanF_segs_in_hull) in R; [discriminate R|].
    destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Section RUNP.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S ra0 tp tsdp P top bot : word) (T tctx n SPB nf : Z) (D : nat).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  #[local] Abbreviation c := (class_of (needed n)).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = Z_to_bv 64 n.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T)) /\ T + 4096 <= U S - 3584 /\ T mod 8 = 0)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  Hypothesis GSPB : (0 <= SPB /\ SPB + 2 ^ 37 < 2 ^ 64)%Z.
  (* [comment removed for export] *)
  Hypothesis GSPB2 : (SPB + 2 ^ 37 + 4096 < 2 ^ 47)%Z /\ (SPB mod 2 ^ 16 = 0)%Z /\ (0x10007fff8000 <= SPB)%Z.
  Hypothesis GTS : (T + 4096 <= SPB \/ SPB + 2 ^ 37 + 4096 <= T)%Z.
  Hypothesis GctxR : (tctx + 4096 <= SPB + 2 ^ 37 \/ SPB + 2 ^ 37 + 4096 <= tctx)%Z.
  Hypothesis G1M : (SPB + 2 ^ 37 + 4096 + 208 <= U S - 2272)%Z.
  Hypothesis Hnf : (0 <= nf <= 2 ^ 27)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn ASEGS mem (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS mem (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn ASEGS mem (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_pg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 P).
  Hypothesis C_P : rdn ASEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn ASEGS mem (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn ASEGS mem (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn ASEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn ASEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn ASEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_rss : rdn ASEGS mem (Z_to_bv 64 0x1897e2) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_lmag : rdn ASEGS mem (Z_to_bv 64 0x10490) 8 = Some (LE8 MAGICw).
  Hypothesis C_tbl2 : rdn ASEGS mem (at_ (Z_to_bv 64 0x10500) 4) 1 = Some [Z_to_bv 8 3].
  Hypothesis C_t16 : rdn ASEGS mem (at_ (Z_to_bv 64 0x10600) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis C_t2048 : rdn ASEGS mem (at_ (Z_to_bv 64 0x10600) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis C_minrz : rdn ASEGS mem (at_ (Z_to_bv 64 0x103f18) 3624) 2 = Some (LE2 16).
  Hypothesis C_maxrz : rdn ASEGS mem (at_ (Z_to_bv 64 0x103f18) 3626) 2 = Some (LE2 2048).
  Hypothesis C_maxsz : rdn ASEGS mem (at_ (Z_to_bv 64 0x103f18) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  Hypothesis C_sbeg : rdn ASEGS mem (at_ (Z_to_bv 64 0x103f18) 32) 8 = Some (LE8 (Z_to_bv 64 SPB)).
  (* [comment removed for export] *)
  Hypothesis C_Tw : store_ok ASEGS mem thr 4096 = true.
  Hypothesis C_unw : rdn ASEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_sw : rdn ASEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn ASEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn ASEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_T0 : rdn ASEGS mem thr 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn ASEGS mem (at_ ctxw 8) 4 = Some (LE4 0).
  Hypothesis C_cnt0 : rdn ASEGS mem (at_ thr (208 + 80 * c)) 4 = Some (LE4 0).          (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[local] Abbreviation RIz := (SPB + 2 ^ 37 + 128 * class_of (needed n))%Z.
  #[local] Abbreviation RI := (Z_to_bv 64 (SPB + 2 ^ 37 + 128 * class_of (needed n))).
  #[local] Abbreviation FABz := (SPB + class_of (needed n) * 2 ^ 32 + 3758096384)%Z.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.


  Lemma nfacts : (24 <= needed n <= 65536)%Z /\ (needed n mod 8 = 0)%Z /\ (16 <= rz n <= 1024)%Z /\ (needed n = rounded n + rz n)%Z
             /\ (Z.max n 8 <= rounded n <= Z.max n 8 + 7)%Z /\ (1 <= c <= 30)%Z.
  Proof using GSPB Gn GS SPB S.
    pose proof (needed_facts n Gn) as [N1 N2]. pose proof (rz_log_range n) as RL.
    assert (Hrz : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    split; [lia|]. split; [exact N2|]. split; [exact Hrz|]. split; [reflexivity|]. split.
    - (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia.
    - apply AsArith3.class_of_range. lia.
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Theorem run_mA_pre :
    exists (r2 r3 : bvmap 5 word) (MP : word -> option byte) (s : Z) (bsz : list byte) (x18 x19 : word),
      let MA := ma_A MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) in
      msteps ASEGS (mkst R (Z_to_bv 64 0x6e4cc) mem rom) (mkst r3 (Z_to_bv 64 0x509cc) (amh_mem ARB r2 MA (at_ S (-2272))) rom)
      (* [comment removed for export] *)
      /\ getr r3 1 = Z_to_bv 64 0x5052c /\ getr r3 2 = at_ S (-2320) /\ getr r3 10 = at_ thr 208 /\ getr r3 11 = at_ thr (208 + 80 * c)
      /\ getr r3 12 = Z_to_bv 64 0x103f18 /\ getr r3 13 = Z_to_bv 64 c /\ getr r3 8 = Z_to_bv 64 c /\ getr r3 9 = at_ thr (208 + 80 * c)
      /\ getr r3 18 = Z_to_bv 64 8 /\ getr r3 19 = at_ thr 208 /\ getr r3 20 = Z_to_bv 64 0x103f18 /\ getr r3 26 = thr
      /\ (forall i : reg, In i [3; 4; 21; 22; 23; 24; 25; 27] -> getr r3 i = getr r2 i)
      (* [comment removed for export] *)
      /\ getr r2 2 = at_ S (-2272) /\ getr r2 3 = getr R 3 /\ getr r2 4 = tp /\ getr r2 8 = Z_to_bv 64 1 /\ getr r2 9 = Z_to_bv 64 n
      /\ getr r2 18 = Z_to_bv 64 8 /\ getr r2 19 = Z_to_bv 64 (needed n) /\ getr r2 20 = Z_to_bv 64 (rz n) /\ getr r2 21 = Z_to_bv 64 n
      /\ getr r2 22 = Z_to_bv 64 0x103f18 /\ getr r2 23 = at_ S (-2128) /\ getr r2 24 = Z_to_bv 64 18446744073709551608
      /\ getr r2 25 = Z_to_bv 64 7 /\ getr r2 27 = Z_to_bv 64 1
      (* [comment removed for export] *)
      /\ (1 <= s <= 30 /\ bytes_le_to_Z bsz = s)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z)
      /\ mem_grows mem MP
      /\ rdn ASEGS MP (at_ S (-2120)) 4 = Some (LE4 s) /\ rdn ASEGS MP (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn ASEGS MP (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (kk : Z) (v : word),
            In (kk, v) [(-8, ra0); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
            rdn ASEGS MP (at_ S kk) 8 = Some (LE8 v)).
  Proof using Hfpc C_cnt0 C_bot C_top C_sw C_unw C_Tw C_maxsz C_maxrz C_minrz C_t2048 C_t16 C_tbl2 C_lmag C_rss C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_inited C_fum C_gcf C_mcs Hstk Hnf G1M GTS GSPB2 GSPB Gbot Gtop GP Gtsdp Gtp Gctx GT Gn GS HR10 HR4 HR2 HR1 nf SPB tctx bot top P tsdp.
    wm_parts GT. wm_parts Gctx.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr. pose proof (u64_range P) as HPr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2 & GT3). destruct Gctx as (Gc1 & Gc2 & Gc3). destruct Gtp as (Gtp1 & Gtp2).
    pose proof nfacts as (NF1 & NF2 & NF3 & NF4 & NF5 & NF6).
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Uctx : U ctxw = tctx) by (unorm; reflexivity).
    (* [comment removed for export] *)
    assert (MH : mpH ASEGS asan_mp_tab mem S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs asan_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x1990a8) 34) with (Z_to_bv 64 0x1990ca : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (UH : uiH ASEGS asan_ui_tab mem (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi asan_ui_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_unw.
      - eapply (store_ok_sub ASEGS mem thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - exact C_pg.
      - exact C_P.
      - rewrite !at_at. eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (GH : gctH ASEGS (ut_gct asan_ui_tab) mem (at_ S (-2208)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct asan_ui_tab gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - exact C_kif. - exact C_key. - exact C_tsdp. - exact C_tctx. - exact C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH ASEGS mem thr top bot).
    { split; [exact C_sw | exact C_top | exact C_bot | exact Gbot | wd_ulia]. }
    destruct (mp_run ASEGS asan_mp_tab asan_mp_tab_ok R mem rom ra0 S tp (Z_to_bv 64 n) (Z_to_bv 64 0x1990a8) thr top bot tsdp ctxw P (Z_to_bv 8 1)
                HR1 HR2 HR4 HR10 MH UH GH SH Gtop D Hfpc)
      as (r1 & MP & s & RUN1 & A1 & A2 & A4 & A10 & A11 & A8 & A9 & A20 & A21 & AG1 & Hs1 & Hs2 & Psz & Ptag & Ptr & Ppc0 & Pslots & Punw & Pfoot & Pgrows).
    cbn [mt_rb asan_mp_tab] in RUN1, A1.
    rewrite (ARB_lit 451788) in RUN1 by lia. rewrite (ARB_lit 309960) in RUN1 by lia.
    (* [comment removed for export] *)
    assert (QP : forall x : word, (U x < U S - 2272 \/ U S <= U x)%Z -> MP x = mem x).
    { intros x Hx. destruct (decide (MP x = mem x)) as [E|NE]; [exact E|]. exfalso.
      destruct (Pfoot x NE) as [F|F]; [lia|].
      apply NE. replace x with (at_ thr 3168) by (apply bv_eq; rewrite at_u by (rewrite Uthr; lia); rewrite Uthr; lia).
      rewrite (rdn1_off MP (at_ thr 3168) (Z_to_bv 8 0)); [| rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact Punw].
      rewrite (rdn1_off mem (at_ thr 3168) (Z_to_bv 8 0)); [reflexivity | rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact C_unw]. }
    (* [comment removed for export] *)
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    destruct (amA_run ASEGS asan_am_tab asan_am_tab_ok r1 MP rom (at_ ARB 0x6e600) (at_ S (-2128)) (at_ S (-2128)) n A1 A2 A10 A11 Gn)
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    all: (lazymatch goal with |- ?G => let G' := eval cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss asan_am_tab] in G in change_no_check G' end).
    { xq QP C_inited. } { xq QP C_rss. } { xq QP C_lmag. } { xq QP C_tbl2. } { xq QP C_t16. } { xq QP C_t2048. }
    { xq QP C_minrz. } { xq QP C_maxrz. } { xq QP C_maxsz. }
    { rewrite at_at. eapply store_ok_mono; [exact Pgrows|].
      eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { unorm. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    { rewrite at_u by lia. lia. }
    cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss asan_am_tab] in RUN2, B22, B26.
    rewrite (ARB_lit 309960) in RUN2 by lia. rewrite (ARB_lit 310692) in RUN2 by lia.
    rewrite (ma_A_eq MP S n r1 A8 A9 A20 A21) in RUN2.
    (* [comment removed for export] *)
    Ltac r1R AG1 k := rewrite (AG1 k) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 22%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 23%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 24%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 25%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 26%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 27%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    set (MA := ma_A MP S n (getr r1 18) (getr r1 19) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in RUN2.
    assert (QA : forall x : word, (U x < U S - 2280 \/ U S <= U x)%Z -> MA x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). rewrite ma_A_outside; [apply QP; lia | lia | lia]. }
    assert (GRA : mem_grows mem MA) by (eapply mem_grows_trans; [exact Pgrows | (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply ma_A_grows]).
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add] in B2.
    (* [comment removed for export] *)
    destruct GSPB2 as (S2 & S3 & S4).
    assert (B4 : getr r2 4 = tp) by (rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); exact HR4).
    assert (B3 : getr r2 3 = getr R 3) by (rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); reflexivity).
    assert (GH2 : gctH ASEGS asan_gct_tab MA (at_ S (-2272)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - xq QA C_kif. - xq QA C_key. - xq QA C_tsdp. - xq QA C_tctx. - xq QA C_thr.
      - unorm. lia.
      - rewrite at_at. eapply store_ok_mono; [exact GRA|].
        eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    Ltac sokA GRA Hstk := rewrite ?at_at; eapply store_ok_mono; [exact GRA|];
      first [ eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia] ].
    destruct (amB_miss_head ASEGS ARB asan_HAL asan_HCB asan_HCBM ARB_ok asan_gct_tab asan_gct_tab_ok asan_GTRB 0x10470
                ltac:(lia) r2 MA rom (at_ S (-2272)) tp tsdp ctxw thr (Z_to_bv 64 0x103f18) n B2 B4 B19 B22 Gn GH2
                ltac:(sokA GRA Hstk) ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(rewrite Uthr, at_u by lia; lia) ltac:(wd_ulia)
                nf (Z_to_bv 64 SPB)
                ltac:(rewrite Uthr; wd_ulia) ltac:(unorm; first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(wd_ulia) Hnf)
      as (r3 & RUN3 & C1 & C2 & C10 & C11 & C12 & C13 & C8 & C9 & C18 & C19 & C20 & C26 & CK).
    { xq QA C_cnt0. }
    rewrite (ARB_lit 310692) in RUN3 by lia. rewrite (ARB_lit 330188) in RUN3 by lia.
    rewrite (ARB_lit 329004) in C1 by lia. rewrite at_at in C2. cbn [Z.add Z.opp Pos.add] in C2.
    exists r2, r3, MP, s.
    destruct (rdn_defined_ex ASEGS MP (at_ S (-2120)) 8) as [bsz [Rsz Lsz]].
    { intros i Hi. rewrite at_u in Hi by lia. apply Pgrows. apply (store_ok1_heap mem); [wd_ulia|].
      eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584 1); [rewrite at_u; lia | exact Hstk | rewrite at_u by lia; wd_ulia | rewrite at_u by lia; wd_ulia_c]. }
    { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (HBSZ : bytes_le_to_Z bsz = s) by (apply (bsz_val ASEGS MP (at_ S (-2120)) bsz s Rsz Psz); [rewrite at_at; exact Ptag | lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]).
    exists bsz, (getr r1 18), (getr r1 19). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold MA.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2 | exact RUN3]|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - intros x NE. destruct (Pfoot x NE) as [F|F]; [exact F|]. exfalso. apply NE. apply QP. rewrite Uthr in F. lia.
  Qed.
End RUNP.
End FPGen.
End AsAllocMRunP.
Module AsAllocMRunS.
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM7i.AsAllocM7 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM8Rm.AsAllocM7g AsAllocM3m AsAllocM3n AsAllocM3p AsAllocM3q AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove.
Import OSSVerify.glaze.binary_reflection.images.Asan.
Import ListNotations.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
Ltac wm_parts H :=
  let T := type of H in
  lazymatch T with
  | ?A /\ ?B => let H1 := fresh "wmp" in let H2 := fresh "wmp" in
                pose proof (proj1 H) as H1; pose proof (proj2 H) as H2; wm_parts H1; wm_parts H2;
                (lazymatch A with context [or] => clear H1 | _ => idtac end);
                (lazymatch B with context [or] => lazymatch B with _ /\ _ => clear H2 | _ => idtac end | _ => idtac end)
  | _ => idtac
  end.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit. exact Hc. Qed.

(* [comment removed for export] *)
Ltac notin' := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin.
Ltac rch := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notin' end end ]).



Section RUNS.
  Variables (M4 rom : word -> option byte) (r0 rC : bvmap 5 word).
  Variables (S thr ctxw sbeg csz stw tr szw : word) (n cnt k tid : Z) (b1 : byte) (bsz : list byte).
  #[local] Abbreviation c := (class_of (needed n)).
  #[local] Abbreviation sp2 := (at_ S (-2272)).
  #[local] Abbreviation cache := (at_ thr 208).
  #[local] Abbreviation inst := (Z_to_bv 64 0x103f18 : word).
  Definition ms_ab : Z := (U sbeg + c * 2 ^ 32 + 16 * k)%Z.
  #[local] Abbreviation m := (Z_to_bv 64 ms_ab).
  Definition ms_MB : word -> option byte := wbytes (wbytes M4 (at_ thr (208 + 80 * c)) (LE4 (cnt - 1))) (at_ thr 2784) (LE8 (v_add stw csz)).
  (* [comment removed for export] *)
  Hypothesis HC1 : getr rC 1 = at_ ARB 0x4bdc4.
  Hypothesis HC2 : getr rC 2 = sp2.
  Hypothesis HC9 : getr rC 9 = Z_to_bv 64 n.
  Hypothesis HC19 : getr rC 19 = Z_to_bv 64 (needed n).
  Hypothesis HC20 : getr rC 20 = Z_to_bv 64 (rz n).
  Hypothesis R8 : getr r0 8 = Z_to_bv 64 c.
  Hypothesis R2 : getr r0 2 = at_ sp2 (-48).
  Hypothesis R9 : getr r0 9 = at_ cache (80 * c).
  Hypothesis R18 : getr r0 18 = Z_to_bv 64 8.
  Hypothesis R19 : getr r0 19 = cache.
  Hypothesis R20 : getr r0 20 = inst.
  Hypothesis R10 : getr r0 10 = Z_to_bv 64 1.
  Hypothesis R21 : getr r0 21 = Z_to_bv 64 n.
  Hypothesis R23 : getr r0 23 = at_ S (-2128).
  Hypothesis R25 : getr r0 25 = Z_to_bv 64 7.
  Hypothesis R26 : getr r0 26 = thr.
  Hypothesis R27 : getr r0 27 = Z_to_bv 64 1.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47)%Z.
  Hypothesis Gn : (1 <= n <= 64512)%Z.
  Hypothesis Gcnt : (1 <= cnt <= 16)%Z.
  Hypothesis Gk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Gtid : (0 <= tid < 2 ^ 31)%Z.
  Hypothesis GT : ((4096 <= U thr /\ hideW (U thr + 4096 <= AIMGLO \/ AIMGHI <= U thr)) /\ U thr + 4096 <= U S - 3584 /\ U thr mod 8 = 0)%Z.
  Hypothesis Gctx : (1 <= U ctxw /\ U ctxw + 4096 <= U S - 3584 /\ (U ctxw + 4096 <= U thr \/ U thr + 4096 <= U ctxw))%Z.
  Hypothesis Gsb : (U sbeg + 2 ^ 37 < 2 ^ 64)%Z.
  Hypothesis Gab : (ms_ab mod 16 = 0 /\ 0x10007fff8000 <= ms_ab /\ ms_ab + needed n <= U S - 3584 /\ ms_ab + 2 ^ 17 <= 2 ^ 47)%Z.
  Hypothesis GabT : (ms_ab + needed n <= U thr \/ U thr + 4096 <= ms_ab)%Z.
  Hypothesis Gabctx : (ms_ab + needed n <= U ctxw \/ U ctxw + 4096 <= ms_ab)%Z.
  (* [comment removed for export] *)
  Hypothesis Rcnt : rdn ASEGS M4 (at_ cache (80 * c)) 4 = Some (LE4 cnt).
  Hypothesis Rcsz : rdn ASEGS M4 (at_ cache (80 * c + 8)) 8 = Some (LE8 csz).
  Hypothesis Rk : rdn ASEGS M4 (at_ cache (80 * c + 16 + 4 * (cnt - 1))) 4 = Some (LE4 k).
  Hypothesis Rst : rdn ASEGS M4 (at_ cache 2576) 8 = Some (LE8 stw).
  Hypothesis SOKT : store_ok ASEGS M4 thr 4096 = true.
  Hypothesis Rsb : rdn ASEGS M4 (at_ inst 32) 8 = Some (LE8 sbeg).
  Hypothesis FR : forall (o : Z) (v : word), In (o, v) (cb_slots2 rC (at_ ARB 0x4bdc4)) -> rdn ASEGS M4 (at_ sp2 o) 8 = Some (LE8 v).
  Hypothesis Rb1 : rdn ASEGS M4 (at_ m (rz n - 15)) 1 = Some [b1].
  Hypothesis SOKh : store_ok ASEGS M4 (at_ m (rz n - 16)) 16 = true.
  Hypothesis R16 : rdn ASEGS M4 (at_ sp2 16) 8 = Some (LE8 (Z_to_bv 64 16)).
  Hypothesis RT0 : rdn ASEGS M4 thr 8 = Some (LE8 ctxw).
  Hypothesis Rtid : rdn ASEGS M4 (at_ ctxw 8) 4 = Some (LE4 tid).
  Hypothesis Rtr : rdn ASEGS M4 (at_ S (-2128)) 8 = Some (LE8 tr).
  Hypothesis Rsz : rdn ASEGS M4 (at_ (at_ S (-2128)) 8) 8 = Some bsz.
  Hypothesis Hsz : lez bsz = U szw /\ length bsz = 8%nat.

  Lemma ms_MB_outside : forall x : word, (U x < U thr + 208 + 80 * c \/ U thr + 208 + 80 * c + 4 <= U x)%Z ->
    (U x < U thr + 2784 \/ U thr + 2792 <= U x)%Z -> ms_MB x = M4 x.
  Proof using Hsz Gab GT Gn GS bsz k szw sbeg S.
    intros x X1 X2. destruct GT as ((T1 & _) & T2 & _). destruct GS as [S1 S2]. pose proof (u64_range thr). pose proof (AsArith3.class_of_range (needed n) ltac:(pose proof (needed_facts n Gn); lia)) as Hc.
    (lazymatch goal with |- ?G => let G' := eval unfold ms_MB in G in change_no_check G' end). rewrite !wbytes_outside; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); try lia. reflexivity.
  Qed.
  Lemma ms_MB_grows : mem_grows M4 ms_MB.
  Proof using. (lazymatch goal with |- ?G => let G' := eval unfold ms_MB in G in change_no_check G' end). eapply mem_grows_trans; apply wbytes_grows. Qed.

  Theorem run_mA_suf :
    exists r : bvmap 5 word,
      msteps ASEGS (mkst r0 (Z_to_bv 64 0x5052c) M4 rom) (mkst r (Z_to_bv 64 0x8ea80) (amC_mem ms_MB m b1 n) rom)
      /\ getr r 1 = Z_to_bv 64 0x4bed0 /\ getr r 2 = sp2 /\ getr r 10 = tr /\ getr r 11 = szw
      /\ getr r 8 = getr rC 8 /\ getr r 9 = Z_to_bv 64 n /\ getr r 18 = m /\ getr r 19 = Z_to_bv 64 (needed n)
      /\ getr r 20 = at_ m (rz n) /\ getr r 21 = at_ m (rz n - 16) /\ getr r 24 = Z_to_bv 64 (tid * 2 ^ 32) /\ getr r 25 = at_ m (rz n + n)
      /\ (forall i : reg, In i [3; 4; 22; 23; 26; 27] -> getr r i = getr r0 i).
  Proof using Hsz Rsz Rtr Rtid RT0 R16 SOKh Rb1 FR Rsb SOKT Rst Rk Rcsz Rcnt Gabctx GabT Gab Gsb Gctx GT Gtid Gk Gcnt Gn GS R27 R26 R25 R23 R21 R10 R20 R19 R18 R9 R2 R8 HC20 HC19 HC9 HC2 HC1 bsz ctxw.
    destruct GS as [S1 S2]. destruct GT as ((T1 & T1b) & T2 & T3). destruct Gctx as (C1 & C2 & C3). destruct Gab as (A1 & A2 & A3 & A4).
    pose proof (u64_range S) as HSr. pose proof (u64_range thr) as Hthr. pose proof (u64_range ctxw) as Hcr. pose proof (u64_range sbeg) as Hsr.
    pose proof (needed_facts n Gn) as [NF1 NF2].
    pose proof (AsArith3.class_of_range (needed n) ltac:(lia)) as Hc.
    assert (Um : U m = ms_ab) by (unorm; reflexivity).
    assert (Hrz : (16 <= rz n <= 1024)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rz in G in change_no_check G' end). pose proof (rz_log_range n). destruct (rz_log_cases n ltac:(lia)) as [[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[[C E]|[C E]]]]]]]]; rewrite E; lia. }
    assert (Hnd : (needed n = rounded n + rz n)%Z) by reflexivity.
    assert (Hrd2 : (8 <= rounded n)%Z).
    { (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). pose proof (Z.div_mod (Z.max n 8 + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (Z.max n 8 + 8 - 1) 8 ltac:(lia)). lia. }
    assert (RETC : ret_ok (at_ ARB 0x4bdc4)) by (rewrite (ARB_lit 0x4bdc4) by lia; apply ret_ok_lit; [lia | reflexivity]).
    (* [comment removed for export] *)
    destruct (cbR2 ASEGS ARB asan_HCB asan_HCBM ARB_ok rC M4 rom (at_ ARB 0x4bdc4) sp2 cache inst RETC HC1 HC2
                ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) M4 r0 c cnt k csz stw sbeg (Z_to_bv 64 1) R8 R2 R9 R18 R19 R20 R10 ltac:(wd_ulia) Hc Gcnt Gk Rcnt Rcsz Rk Rst)
      as (rB & RUNB & B10 & B13 & BK & BK2).
    { eapply (store_ok_sub ASEGS M4 thr _ 4096); [lia | exact SOKT | rewrite !at_at, at_u by lia; lia | rewrite !at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply (store_ok_sub ASEGS M4 thr _ 4096); [lia | exact SOKT | rewrite !at_at, at_u by lia; lia | rewrite !at_at, at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { exact Rsb. }
    { exact FR. }
    { rewrite at_u by lia. rewrite <- Zplus_mod_idemp_l, T3. reflexivity. }
    { rewrite at_u by lia. unorm. unfold hideW in T1b. lia. }
    { rewrite !at_u by lia. lia. }
    { unorm. lia. }
    { exact Gsb. }
    cbv zeta in RUNB. rewrite !at_at in RUNB. replace (208 + 2576)%Z with 2784%Z in RUNB by reflexivity.
    change (wbytes (wbytes M4 _ _) _ _) with ms_MB in RUNB.
    (* [comment removed for export] *)
    assert (QB : forall x : word, (U x < U thr \/ U thr + 4096 <= U x)%Z -> ms_MB x = M4 x) by (intros x Hx; apply ms_MB_outside; lia).
    Ltac xqs QB H := eapply rd_same; [ intros x Hx; apply QB; revert Hx; rewrite ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                                       | rewrite ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia | exact H ].
    destruct (amC_run ASEGS ARB asan_HAL2 rB ms_MB rom sp2 m (at_ S (-2128)) thr ctxw tr szw bsz b1 n tid)
      as (r4 & RUN4 & E1 & E10 & E11 & E18 & E20 & E21 & E24 & E25 & AG4).
    { rewrite (BK 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC2. }
    { rewrite (BK 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC9. }
    { rewrite B10. apply bv_eq. (lazymatch goal with |- ?G => let G' := eval unfold ms_ab in G in change_no_check G' end). unorm. reflexivity. }
    { rewrite (BK 19%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC19. }
    { rewrite (BK 20%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact HC20. }
    { rewrite (BK2 21%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R21. }
    { rewrite (BK2 23%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R23. }
    { rewrite (BK2 25%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R25. }
    { rewrite (BK2 26%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R26. }
    { rewrite (BK2 27%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])). exact R27. }
    { exact Gn. } { exact Gtid. }
    { rewrite Um. lia. } { rewrite at_u by lia. lia. } { split; [split; [exact T1 | exact T1b] | lia]. } { lia. } { rewrite at_u by lia. lia. }
    { assert (Uh : U (at_ m (rz n - 15)) = (ms_ab + rz n - 15)%Z) by (rewrite at_u by (rewrite Um; lia); rewrite Um; lia).
      eapply rd_same; [ | | exact Rb1]; [intros x Hx; apply QB; rewrite Uh in Hx; cbn in Hx; lia | rewrite Uh; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { eapply store_ok_mono; [apply ms_MB_grows | exact SOKh]. }
    { xqs QB R16. }
    { (lazymatch goal with |- ?G => let G' := eval unfold ms_MB in G in change_no_check G' end). rewrite !rdn_wbytes_out; [exact RT0 | ..]; wd_lenlit; rewrite ?length_N_to_le_bytes, ?at_at, ?at_u by lia; (lazymatch goal with |- ?G => let G' := eval cbn [length Z.of_nat Pos.of_succ_nat Pos.succ Pos.to_nat] in G in change_no_check G' end); lia. }
    { xqs QB Rtid. }
    { xqs QB Rtr. }
    { xqs QB Rsz. }
    { exact Hsz. }
    { rewrite at_u, Um by lia. lia. }
    { rewrite Um. lia. }
    { rewrite Um. lia. }
    { rewrite at_u, Um by lia. lia. }
    rewrite (ARB_lit 310724) in RUN4 by lia. rewrite (ARB_lit 584320) in RUN4 by lia. rewrite (ARB_lit 329004) in RUNB by lia. rewrite (ARB_lit 310724) in RUNB by lia.
    exists r4. split; [eapply msteps_trans; [exact RUNB | exact RUN4]|].
    split; [rewrite E1; apply ARB_lit; lia|].
    split; [rewrite (AG4 2%bv) by notin; rewrite (BK 2%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact HC2|].
    split; [exact E10|]. split; [exact E11|].
    split; [rewrite (AG4 8%bv) by notin; apply BK; (lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])|].
    split; [rewrite (AG4 9%bv) by notin; rewrite (BK 9%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact HC9|].
    split; [exact E18|].
    split; [rewrite (AG4 19%bv) by notin; rewrite (BK 19%bv) by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); repeat (first [left; reflexivity | right])); exact HC19|].
    split; [exact E20|]. split; [exact E21|]. split; [exact E24|]. split; [exact E25|].
    intros i Hi. rewrite (AG4 i); [apply BK2; cbn [In] in Hi |- *; clear - Hi; tauto|].
    cbn [In] in Hi. intros Hx. cbn [In] in Hx. repeat (destruct Hi as [<-|Hi]; [repeat (destruct Hx as [Hx|Hx]; [discriminate Hx|]); exact Hx|]). exact Hi.
  Qed.
End RUNS.
End FPGen.
End AsAllocMRunS.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.AsArith3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAinvDefs3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtUnwind OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2.AsAllocM0 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM1 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM2 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM3 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM4 OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA.AsAllocMI OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocMMemA AsAllocMIm OSSVerify.Proofs.glaze.binary_reflection.lib.MuslMemmove AsAllocM2s AsAllocM9e OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9a OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocM9b.AsAllocM9d.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsAllocFHyp.AsAllocMTag.
From OSSVerify.glaze.binary_reflection.images Require Import Asan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import AmLia.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Ltac wm_clear_disj_or T := lazymatch T with | _ \/ _ => idtac | ?A /\ ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A <-> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] | ?A -> ?B => first [wm_clear_disj_or A | wm_clear_disj_or B] end.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.   (* [comment removed for export] *)
Ltac wm_clear_disj := am_wm_clear_disj.   (* [comment removed for export] *)
Ltac wm_lia0 := tryif noncert_goal_has_var then (Zify.zify; xlia zchecker)
                else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac am_inner ::= first [ solve [wm_clear_disj; wm_lia0] | wm_lia0 ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Ltac wm_parts H :=
  let T := type of H in
  lazymatch T with
  | ?A /\ ?B => let H1 := fresh "wmp" in let H2 := fresh "wmp" in
                pose proof (proj1 H) as H1; pose proof (proj2 H) as H2; wm_parts H1; wm_parts H2;
                (lazymatch A with context [or] => clear H1 | _ => idtac end);
                (lazymatch B with context [or] => lazymatch B with _ /\ _ => clear H2 | _ => idtac end | _ => idtac end)
  | _ => idtac
  end.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).
#[local] Abbreviation LE2 z := (word_to_le_bytes 2 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

Lemma at0_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ (Z_to_bv 64 0) c = Z_to_bv 64 c.
Proof using. intros c Hc. apply bv_eq. rewrite at_u by (first [ solve [ wd_unorm1; wd_zofnat; lia ] | rewrite u_Z2bv by lia; lia ]). rewrite !u_Z2bv by lia. reflexivity. Qed.
Lemma ARB_lit : forall c : Z, (0 <= c < 2 ^ 64)%Z -> at_ ARB c = Z_to_bv 64 c.
Proof using. intros c Hc. (lazymatch goal with |- ?G => let G' := eval unfold ARB in G in change_no_check G' end). apply at0_lit. exact Hc. Qed.

(* [comment removed for export] *)
Ltac notin' := try (lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); try (lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin.
Ltac rch := repeat (first [ reflexivity | assumption
                          | match goal with |- getr ?r ?i = _ => match goal with H : getr r i = _ |- _ => rewrite H end end
                          | match goal with |- getr ?r ?i = _ => match goal with AG : regs_agree _ _ r |- _ => rewrite (AG i) by notin' end end ]).

(* [comment removed for export] *)
Lemma rdn1_off : forall (m : mem) (a : word) b,
  (bv_unsigned a + 1 <= 0x10000 \/ 0x65d000 <= bv_unsigned a)%Z -> rdn ASEGS m a 1 = Some [b] -> m a = Some b.
Proof using.
  intros m a b Ha R. cbn [rdn] in R. destruct (m a) as [b'|] eqn:E.
  - cbn in R. congruence.
  - unfold seg_rom, memory_read in R. change (Z.of_N 1) with 1%Z in R.
    rewrite (find_segment1_none_outside ASEGS 0x10000 0x65d000 (bv_unsigned a) asanF_segs_in_hull) in R; [discriminate R|].
    destruct Ha as [Ha|Ha]; [left | right]; lia.
Qed.

Section RUNS1.
  Variables (mem rom : word -> option byte) (R : bvmap 5 word).
  Variables (S ra0 tp tsdp P top bot name : word) (T tctx n : Z) (D : nat).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  #[local] Abbreviation ctxw := (Z_to_bv 64 tctx).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis HR1 : getr R 1 = ra0.
  Hypothesis HR2 : getr R 2 = S.
  Hypothesis HR4 : getr R 4 = tp.
  Hypothesis HR10 : getr R 10 = Z_to_bv 64 n.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gn : (64513 <= n <= 2 ^ 34)%Z.
  (* [comment removed for export] *)
  Hypothesis GT : ((4096 <= T /\ (T + 4096 <= AIMGLO \/ AIMGHI <= T)) /\ T + 4096 <= U S - 3584 /\ T mod 8 = 0)%Z.
  Hypothesis Gctx : (1 <= tctx /\ tctx + 4096 <= U S - 3584 /\ (tctx + 4096 <= T \/ T + 4096 <= tctx))%Z.
  Hypothesis Gtp : (AIMGLO + 88 <= U tp /\ U tp + 8 <= AIMGHI)%Z.
  Hypothesis Gtsdp : (AIMGLO <= U tsdp /\ U tsdp + 8 <= AIMGHI)%Z.
  Hypothesis GP : (AIMGLO <= U P /\ U P + 8 <= AIMGHI)%Z.
  Hypothesis Gtop : (4096 <= U top <= 2 ^ 47)%Z.
  Hypothesis Gbot : (U bot < U top)%Z.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok ASEGS mem (at_ S (-3584)) 3584 = true.
  (* [comment removed for export] *)
  Hypothesis C_mcs : rdn ASEGS mem (Z_to_bv 64 0x10827c) 4 = Some (LE4 30).
  Hypothesis C_gcf : rdn ASEGS mem (Z_to_bv 64 0xff260) 8 = Some (LE8 (Z_to_bv 64 0x1990a8)).
  Hypothesis C_fum : rdn ASEGS mem (Z_to_bv 64 0x1990ca) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_inited : rdn ASEGS mem (Z_to_bv 64 0x108258) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_pg : rdn ASEGS mem (Z_to_bv 64 0xff250) 8 = Some (LE8 P).
  Hypothesis C_P : rdn ASEGS mem P 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_kif : rdn ASEGS mem (Z_to_bv 64 0x106de0) 1 = Some [Z_to_bv 8 1].
  Hypothesis C_key : rdn ASEGS mem (at_ (Z_to_bv 64 0x106de0) 4) 4 = Some (LE4 0).
  Hypothesis C_tsdp : rdn ASEGS mem (at_ tp (-88)) 8 = Some (LE8 tsdp).
  Hypothesis C_tctx : rdn ASEGS mem tsdp 8 = Some (LE8 ctxw).
  Hypothesis C_thr : rdn ASEGS mem (at_ ctxw 152) 8 = Some (LE8 thr).
  Hypothesis C_rss : rdn ASEGS mem (Z_to_bv 64 0x1897e2) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_lmag : rdn ASEGS mem (Z_to_bv 64 0x10490) 8 = Some (LE8 MAGICw).
  Hypothesis C_tbl2 : rdn ASEGS mem (at_ (Z_to_bv 64 0x10500) 4) 1 = Some [Z_to_bv 8 3].
  Hypothesis C_t16 : rdn ASEGS mem (at_ (Z_to_bv 64 0x10600) 8) 1 = Some [Z_to_bv 8 4].
  Hypothesis C_t2048 : rdn ASEGS mem (at_ (Z_to_bv 64 0x10600) 49) 1 = Some [Z_to_bv 8 11].
  Hypothesis C_minrz : rdn ASEGS mem (at_ (Z_to_bv 64 0x103f18) 3624) 2 = Some (LE2 16).
  Hypothesis C_maxrz : rdn ASEGS mem (at_ (Z_to_bv 64 0x103f18) 3626) 2 = Some (LE2 2048).
  Hypothesis C_maxsz : rdn ASEGS mem (at_ (Z_to_bv 64 0x103f18) 3616) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 40))).
  (* [comment removed for export] *)
  Hypothesis C_ipg : rdn ASEGS mem (Z_to_bv 64 (0x103f18 + 64)) 8 = Some (LE8 (Z_to_bv 64 4096)).
  Hypothesis C_gnm : rdn ASEGS mem (Z_to_bv 64 0xff258) 8 = Some (LE8 (Z_to_bv 64 0x1011e8)).
  Hypothesis C_nm : rdn ASEGS mem (Z_to_bv 64 0x1011e8) 8 = Some (LE8 name).
  (* [comment removed for export] *)
  Hypothesis C_Tw : store_ok ASEGS mem thr 4096 = true.
  Hypothesis C_unw : rdn ASEGS mem (at_ thr 3168) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_sw : rdn ASEGS mem (at_ thr 40) 1 = Some [Z_to_bv 8 0].
  Hypothesis C_top : rdn ASEGS mem (at_ thr 8) 8 = Some (LE8 top).
  Hypothesis C_bot : rdn ASEGS mem (at_ thr 16) 8 = Some (LE8 bot).
  Hypothesis C_T0 : rdn ASEGS mem thr 8 = Some (LE8 ctxw).
  Hypothesis C_tid : rdn ASEGS mem (at_ ctxw 8) 4 = Some (LE4 0).
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis Hfpc : fpc mem (U (getr R 8)) (U S) D.


  Lemma sfacts : (sec_needed n = rounded n + 4096)%Z /\ (n <= rounded n <= n + 7)%Z /\ (rz n = 2048)%Z.
  Proof using Gn GS S.
    assert (Hrz : (rz n = 2048)%Z) by (apply AsArith3.rz_big; lia).
    split; [(lazymatch goal with |- ?G => let G' := eval unfold sec_needed in G in change_no_check G' end); rewrite Hrz; lia|]. split; [| exact Hrz].
    (lazymatch goal with |- ?G => let G' := eval unfold rounded, RoundUp in G in change_no_check G' end). rewrite Z.max_l by lia. pose proof (Z.div_mod (n + 8 - 1) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (n + 8 - 1) 8 ltac:(lia)). lia.
  Qed.

  (* [comment removed for export] *)
  Definition ms_pre_mem (MA : word -> option byte) : word -> option byte :=
    la_m0 (cbs_m0 (wbytes MA (at_ (at_ S (-2272)) (-8)) (LE8 (Z_to_bv 64 0x4bda8)))
                  (at_ S (-2272)) (Z_to_bv 64 0x4bdc4) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048))
          (at_ S (-2320)) (Z_to_bv 64 0x50324) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
          (Z_to_bv 64 n) (Z_to_bv 64 0x103f18) (at_ S (-2128)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 7).

  Theorem run_mS_pre :
    exists (r5 : bvmap 5 word) (MP : word -> option byte) (s : Z) (bsz : list byte) (x18 x19 : word),
      let MA := ma_A MP S n x18 x19 (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27) in
      msteps ASEGS (mkst R (Z_to_bv 64 0x6e4cc) mem rom) (mkst r5 (0x82004 : word) (ms_pre_mem MA) rom)
      (* [comment removed for export] *)
      /\ la_regs (at_ S (-2320)) (Z_to_bv 64 0x1041c8) (sec_needed n) r5 /\ getr r5 1 = Z_to_bv 64 0x50610 /\ getr r5 21 = Z_to_bv 64 8
      /\ getr r5 10 = Z_to_bv 64 (la_msz (sec_needed n)) /\ getr r5 11 = name
      /\ getr r5 3 = getr R 3 /\ getr r5 4 = tp /\ getr r5 26 = thr /\ getr r5 27 = Z_to_bv 64 1
      (* [comment removed for export] *)
      /\ (1 <= s <= 30 /\ bytes_le_to_Z bsz = s)%Z /\ (s <= 2 + Z.of_nat D)%Z
      /\ (forall x : word, MP x <> mem x -> (U S - 2272 <= U x < U S)%Z)
      /\ mem_grows mem MP
      /\ rdn ASEGS MP (at_ S (-2120)) 4 = Some (LE4 s) /\ rdn ASEGS MP (at_ S (-2120)) 8 = Some bsz /\ length bsz = 8%nat
      /\ rdn ASEGS MP (at_ S (-2128)) 8 = Some (LE8 (at_ S (-2112)))
      /\ (forall (kk : Z) (v : word),
            In (kk, v) [(-8, ra0); (-16, getr R 8); (-24, getr R 9); (-32, getr R 18); (-40, getr R 19); (-48, getr R 20); (-56, getr R 21)]%Z ->
            rdn ASEGS MP (at_ S kk) 8 = Some (LE8 v)).
  Proof using Hfpc C_bot C_top C_sw C_unw C_Tw C_nm C_gnm C_ipg C_maxsz C_maxrz C_minrz C_t2048 C_t16 C_tbl2 C_lmag C_rss C_thr C_tctx C_tsdp C_key C_kif C_P C_pg C_inited C_fum C_gcf C_mcs Hstk Gbot Gtop GP Gtsdp Gtp Gctx GT Gn GS HR10 HR4 HR2 HR1 tctx bot top P tsdp.
    wm_parts GT. wm_parts Gctx.
    pose proof (u64_range S) as HSr. pose proof (u64_range tp) as Htpr. pose proof (u64_range tsdp) as Htsr. pose proof (u64_range P) as HPr.
    destruct GS as (GS1 & GS2 & GS3). destruct GT as (GT1 & GT2 & GT3). destruct Gctx as (Gc1 & Gc2 & Gc3). destruct Gtp as (Gtp1 & Gtp2).
    pose proof sfacts as (NF1 & NF2 & NF3).
    assert (Uthr : U thr = T) by (unorm; reflexivity).
    assert (Uctx : U ctxw = tctx) by (unorm; reflexivity).
    (* [comment removed for export] *)
    assert (MH : mpH ASEGS asan_mp_tab mem S (Z_to_bv 64 0x1990a8) thr (Z_to_bv 8 1)).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [mt_rb mt_ui mt_g_cf mt_a_inited mt_g_mcs asan_mp_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_gcf.
      - replace (at_ (Z_to_bv 64 0x1990a8) 34) with (Z_to_bv 64 0x1990ca : word) by (apply bv_eq; reflexivity). exact C_fum.
      - vm_compute. discriminate.
      - exact C_mcs.
      - eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - unorm. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia.
      - lia.
      - rewrite Uthr. lia. }
    assert (UH : uiH ASEGS asan_ui_tab mem (at_ S (-2128)) (at_ S (-2128)) S thr P).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_g_inited ut_g_pgsz ut_img_lo ut_img_hi asan_ui_tab] in G in change_no_check G' end).
      - exact C_inited.
      - exact C_unw.
      - eapply (store_ok_sub ASEGS mem thr _ 4096); [rewrite Uthr; lia | exact C_Tw | rewrite at_u, Uthr; lia | rewrite at_u, Uthr; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - exact C_pg.
      - exact C_P.
      - rewrite !at_at. eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - rewrite !at_at. eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia.
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (GH : gctH ASEGS (ut_gct asan_ui_tab) mem (at_ S (-2208)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [ut_gct asan_ui_tab gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - exact C_kif. - exact C_key. - exact C_tsdp. - exact C_tctx. - exact C_thr.
      - unorm. lia.
      - rewrite !at_at. eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    assert (SH : stkH ASEGS mem thr top bot).
    { split; [exact C_sw | exact C_top | exact C_bot | exact Gbot | wd_ulia]. }
    destruct (mp_run ASEGS asan_mp_tab asan_mp_tab_ok R mem rom ra0 S tp (Z_to_bv 64 n) (Z_to_bv 64 0x1990a8) thr top bot tsdp ctxw P (Z_to_bv 8 1)
                HR1 HR2 HR4 HR10 MH UH GH SH Gtop D Hfpc)
      as (r1 & MP & s & RUN1 & A1 & A2 & A4 & A10 & A11 & A8 & A9 & A20 & A21 & AG1 & Hs1 & Hs2 & Psz & Ptag & Ptr & Ppc0 & Pslots & Punw & Pfoot & Pgrows).
    cbn [mt_rb asan_mp_tab] in RUN1, A1.
    rewrite (ARB_lit 451788) in RUN1 by lia. rewrite (ARB_lit 309960) in RUN1 by lia.
    (* [comment removed for export] *)
    assert (QP : forall x : word, (U x < U S - 2272 \/ U S <= U x)%Z -> MP x = mem x).
    { intros x Hx. destruct (decide (MP x = mem x)) as [E|NE]; [exact E|]. exfalso.
      destruct (Pfoot x NE) as [F|F]; [lia|].
      apply NE. replace x with (at_ thr 3168) by (apply bv_eq; rewrite at_u by (rewrite Uthr; lia); rewrite Uthr; lia).
      rewrite (rdn1_off MP (at_ thr 3168) (Z_to_bv 8 0)); [| rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact Punw].
      rewrite (rdn1_off mem (at_ thr 3168) (Z_to_bv 8 0)); [reflexivity | rewrite at_u, Uthr by (rewrite Uthr; lia); lia | exact C_unw]. }
    (* [comment removed for export] *)
    Ltac xq Q H :=
      eapply rd_same; [ intros x Hx; apply Q; revert Hx; (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); intros Hx; lia
                      | (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); first [ solve [ wd_unorm1; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); wd_zofnat; lia ] | unorm; (lazymatch goal with |- ?G => let G' := eval cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in G in change_no_check G' end); lia ] | exact H ].
    destruct (amA_run_s ASEGS asan_am_tab asan_am_tab_ok r1 MP rom (at_ ARB 0x6e600) (at_ S (-2128)) (at_ S (-2128)) n A1 A2 A10 A11 Gn)
      as (r2 & RUN2 & B2 & B8 & B9 & B18 & B19 & B20 & B21 & B22 & B23 & B24 & B25 & B26 & B27 & AG2).
    all: (lazymatch goal with |- ?G => let G' := eval cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss asan_am_tab] in G in change_no_check G' end).
    { xq QP C_inited. } { xq QP C_rss. } { xq QP C_lmag. } { xq QP C_tbl2. } { xq QP C_t16. } { xq QP C_t2048. }
    { xq QP C_minrz. } { xq QP C_maxrz. } { xq QP C_maxsz. }
    { rewrite at_at. eapply store_ok_mono; [exact Pgrows|].
      eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { unorm. rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    { rewrite at_u by lia. lia. }
    cbn [am_rb am_inst am_g_magic am_tbl2 am_tbl am_g_inited am_g_rss asan_am_tab] in RUN2, B22, B26.
    rewrite (ARB_lit 309960) in RUN2 by lia. rewrite (ARB_lit 310692) in RUN2 by lia.
    rewrite (ma_A_eq MP S n r1 A8 A9 A20 A21) in RUN2.
    rewrite (AG1 22%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 23%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 24%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 25%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    rewrite (AG1 26%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin). rewrite (AG1 27%bv) in RUN2 by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin).
    set (MA := ma_A MP S n (getr r1 18) (getr r1 19) (getr R 22) (getr R 23) (getr R 24) (getr R 25) (getr R 26) (getr R 27)) in RUN2.
    assert (QA : forall x : word, (U x < U S - 2280 \/ U S <= U x)%Z -> MA x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end). rewrite ma_A_outside; [apply QP; lia | lia | lia]. }
    assert (GRA : mem_grows mem MA) by (eapply mem_grows_trans; [exact Pgrows | (lazymatch goal with |- ?G => let G' := eval unfold MA in G in change_no_check G' end); apply ma_A_grows]).
    rewrite at_at in B2. cbn [Z.add Z.opp Pos.add] in B2.
    (* [comment removed for export] *)
    assert (B4 : getr r2 4 = tp) by (rewrite (AG2 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 4%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); exact HR4).
    assert (B3 : getr r2 3 = getr R 3) by (rewrite (AG2 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold am_clobx in G in change_no_check G' end); notin); rewrite (AG1 3%bv) by ((lazymatch goal with |- ?G => let G' := eval unfold mp_clobx in G in change_no_check G' end); notin); reflexivity).
    assert (GH2 : gctH ASEGS asan_gct_tab MA (at_ S (-2272)) tp tsdp ctxw thr).
    { split; (lazymatch goal with |- ?G => let G' := eval cbn [gt_tsd asan_gct_tab] in G in change_no_check G' end).
      - xq QA C_kif. - xq QA C_key. - xq QA C_tsdp. - xq QA C_tctx. - xq QA C_thr.
      - unorm. lia.
      - rewrite at_at. eapply store_ok_mono; [exact GRA|].
        eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia].
      - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. - (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); unorm. lia. }
    destruct (ambs_glue ASEGS ARB asan_HAL asan_gct_tab asan_gct_tab_ok asan_GTRB r2 MA rom (at_ S (-2272)) tp tsdp ctxw thr (Z_to_bv 64 0x103f18)
                (sec_needed n) B2 B4 B19 B22 GH2 ltac:(first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]) ltac:(rewrite Uthr, at_u by lia; lia))
      as (r3 & M1 & RUN3 & EM1 & C1 & C2 & C10 & C11 & C12 & C13 & C26 & CK & AGK).
    rewrite (ARB_lit 310692) in RUN3 by lia. rewrite (ARB_lit 328316) in RUN3 by lia.
    rewrite (ARB_lit 310696) in EM1 by lia. rewrite (ARB_lit 310724) in C1 by lia.
    subst M1.
    replace (Z_to_bv 64 328316 : word) with (0x5027c%bv : word) in RUN3 by (apply bv_eq; reflexivity).
    Ltac viaCK CK H := rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H.
    (* [comment removed for export] *)
    set (M1 := wbytes MA (at_ (at_ S (-2272)) (-8)) (LE8 (Z_to_bv 64 0x4bda8))) in *.
    assert (GR1 : mem_grows mem M1) by (eapply mem_grows_trans; [exact GRA | apply wbytes_grows]).
    assert (Q1 : forall x : word, (U x < U S - 2280 \/ U S <= U x)%Z -> M1 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M1 in G in change_no_check G' end). rewrite wbytes_outside; [apply QA; exact Hx | rewrite length_N_to_le_bytes, !at_u by (rewrite ?at_u; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia | rewrite length_N_to_le_bytes, !at_u by (rewrite ?at_u; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    destruct (cbs_pre M1 rom (at_ S (-2272)) (Z_to_bv 64 0x4bdc4) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
                (sec_needed n) r3 C1 C2 C10 C12 C13 ltac:(viaCK CK B8) ltac:(viaCK CK B9) ltac:(viaCK CK B18) ltac:(viaCK CK B19) ltac:(viaCK CK B20))
      as (r4 & RUN4 & D1 & D2 & D8 & D10 & D11 & D12 & D13 & AG4).
    { rewrite at_u by lia. lia. }
    { lia. }
    { rewrite at_at. eapply store_ok_mono; [exact GR1|].
      eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    rewrite at_at in D2. change (-2272 + -48)%Z with (-2320)%Z in D2.
    set (M2 := cbs_m0 M1 (at_ S (-2272)) (Z_to_bv 64 0x4bdc4) (Z_to_bv 64 0) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)) in *.
    assert (GR2 : mem_grows mem M2) by (eapply mem_grows_trans; [exact GR1 | (lazymatch goal with |- ?G => let G' := eval unfold M2, cbs_m0 in G in change_no_check G' end); do 5 (eapply mem_grows_trans; [| apply wbytes_grows]); apply wbytes_grows]).
    assert (Q2 : forall x : word, (U x < U S - 2320 \/ U S <= U x)%Z -> M2 x = mem x).
    { intros x Hx. (lazymatch goal with |- ?G => let G' := eval unfold M2, cbs_m0 in G in change_no_check G' end). rewrite !wbytes_outside by (rewrite length_N_to_le_bytes, !at_u by (rewrite ?at_u; lia); (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia). apply Q1. lia. }
    (* [comment removed for export] *)
    Ltac via4 AG4 CK H := rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact H.
    destruct (la_pre M2 rom (at_ S (-2320)) (Z_to_bv 64 0x50324) (Z_to_bv 64 8) (Z_to_bv 64 n) (Z_to_bv 64 8) (Z_to_bv 64 (sec_needed n)) (Z_to_bv 64 2048)
                (Z_to_bv 64 n) (Z_to_bv 64 0x103f18) (at_ S (-2128)) (Z_to_bv 64 18446744073709551608) (Z_to_bv 64 7) (Z_to_bv 64 0x1041c8) name
                (sec_needed n) r4 D1 D2 D10 D11 D12 D13 D8 ltac:(via4 AG4 CK B9) ltac:(via4 AG4 CK B18) ltac:(via4 AG4 CK B19) ltac:(via4 AG4 CK B20)
                ltac:(via4 AG4 CK B21) ltac:(via4 AG4 CK B22) ltac:(via4 AG4 CK B23) ltac:(via4 AG4 CK B24) ltac:(via4 AG4 CK B25))
      as (r5 & RUN5 & E_regs & E1 & E21 & E10 & E11 & AG5).
    { rewrite at_u by lia. lia. }
    { lia. }
    { rewrite at_at. eapply store_ok_mono; [exact GR2|].
      eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584); [rewrite at_u; lia | exact Hstk | rewrite !at_u; lia | rewrite !at_u; (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end); lia]. }
    { xq Q2 C_ipg. } { xq Q2 C_gnm. } { xq Q2 C_nm. }
    exists r5, MP, s.
    destruct (rdn_defined_ex ASEGS MP (at_ S (-2120)) 8) as [bsz [Rsz Lsz]].
    { intros i Hi. rewrite at_u in Hi by lia. apply Pgrows. apply (store_ok1_heap mem); [wd_ulia|].
      eapply (store_ok_sub ASEGS mem (at_ S (-3584)) _ 3584 1); [rewrite at_u; lia | exact Hstk | rewrite at_u by lia; wd_ulia | rewrite at_u by lia; wd_ulia_c]. }
    { rewrite at_u by lia. (lazymatch goal with |- ?G => let G' := eval cbn in G in change_no_check G' end). lia. }
    assert (HBSZ : bytes_le_to_Z bsz = s) by (apply (bsz_val ASEGS MP (at_ S (-2120)) bsz s Rsz Psz); [rewrite at_at; exact Ptag | lia | first [ solve [ (lazymatch goal with |- ?G => let G' := eval unfold at_ in G in change_no_check G' end); wd_unorm1; wd_zofnat; lia ] | rewrite at_u by lia; lia ]]).
    exists bsz, (getr r1 18), (getr r1 19). (lazymatch goal with |- ?G => let G' := eval cbv zeta in G in change_no_check G' end). fold MA.
    split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|]; eapply msteps_trans; [exact RUN3|]; eapply msteps_trans; [exact RUN4 | exact RUN5]|].
    split; [exact E_regs|]. split; [exact E1|]. split; [exact E21|]. split; [exact E10|]. split; [exact E11|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact B3|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact B4|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; exact C26|].
    split; [rewrite (AG5 _) by notin; rewrite (AG4 _) by notin; rewrite CK by ((lazymatch goal with |- ?G => let G' := eval cbn [In] in G in change_no_check G' end); auto 20); exact B27|].
    repeat match goal with |- _ /\ _ => split end; try assumption; try lia.
    - intros x NE. destruct (Pfoot x NE) as [F|F]; [exact F|]. exfalso. apply NE. apply QP. rewrite Uthr in F. lia.
  Qed.
End RUNS1.
End FPGen.
