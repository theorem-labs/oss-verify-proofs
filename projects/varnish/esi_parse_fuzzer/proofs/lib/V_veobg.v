(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge ZBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 Img0 V_Vct V_Co10c.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_VSle5.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_World.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_Paq9r R_strcmp.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5.V_VS8yn OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_VSle5 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_World.V_VepKit OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_Paq9r OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.R_strcmp.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun StrFun2.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)


(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma strcmp_walk_nul_l : forall (l r : list byte) i,
  nth_error l i = Some (Z_to_bv 8 0) -> (i < length r)%nat -> exists x, strcmp_walk l r = Some x.
Proof.
  induction l as [|a l IH]; intros r i Hn Hl; [destruct i; discriminate|].
  destruct r as [|b r]; [cbn in Hl; lia|]. cbn [strcmp_walk].
  destruct ((bv_unsigned a =? 0) || negb (bv_unsigned a =? bv_unsigned b))%bool eqn:C; [eexists; reflexivity|].
  destruct i as [|i]; cbn in Hn.
  - injection Hn as ->. cbn in C. discriminate.
  - apply (IH r i Hn). cbn in Hl. lia.
Qed.

(* [comment removed for export] *)
Definition STR_src : list byte := [Z_to_bv 8 115; Z_to_bv 8 114; Z_to_bv 8 99; Z_to_bv 8 61; Z_to_bv 8 0].
Definition STR_onerror : list byte :=
  [Z_to_bv 8 111; Z_to_bv 8 110; Z_to_bv 8 101; Z_to_bv 8 114; Z_to_bv 8 114; Z_to_bv 8 111; Z_to_bv 8 114; Z_to_bv 8 61; Z_to_bv 8 0].
Definition STR_continue : list byte :=
  [Z_to_bv 8 99; Z_to_bv 8 111; Z_to_bv 8 110; Z_to_bv 8 116; Z_to_bv 8 105; Z_to_bv 8 110; Z_to_bv 8 117; Z_to_bv 8 101; Z_to_bv 8 0].
Definition A_src : Z := 0x11841.
Definition A_onerror : Z := 0x102d6.
Definition A_continue : Z := 0x11b94.

Lemma str_src_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_src STR_src.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| unfold A_src, A_onerror, A_continue; lia| cbn [length STR_src STR_onerror STR_continue Z.of_nat Pos.of_succ_nat Pos.succ]; unfold A_src, A_onerror, A_continue; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.
Lemma str_onerror_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_onerror STR_onerror.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| unfold A_src, A_onerror, A_continue; lia| cbn [length STR_src STR_onerror STR_continue Z.of_nat Pos.of_succ_nat Pos.succ]; unfold A_src, A_onerror, A_continue; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.
Lemma str_continue_at : forall m, mem_inv rsegs m -> bytes_at rsegs m A_continue STR_continue.
Proof. intros m MI. apply (ro_bytes_at rsegs m); [exact MI| unfold A_src, A_onerror, A_continue; lia| cbn [length STR_src STR_onerror STR_continue Z.of_nat Pos.of_succ_nat Pos.succ]; unfold A_src, A_onerror, A_continue; lia| apply ro_bytes_b_sound; vm_compute; reflexivity]. Qed.

(* [comment removed for export] *)
Definition lws_post (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (a0' a2' : word) (pc' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0' (Z_to_bv 64 VCT_ADDR) a2' a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (Z_to_bv 64 pc') fc None m (seg_rom rsegs)
    /\ (pc' = 0x1b650 \/ pc' = 0x1b440).

Lemma lws_loop : forall (k : nat) (ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (B : Z) (bs : list byte) (i z : Z) (b : byte),
  u8arr rsegs m B bs -> mem_inv rsegs m ->
  nth_error bs (Z.to_nat i) = Some b -> 0 <= i -> bv_unsigned b <> 0 ->
  nth_error bs (Z.to_nat z) = Some (Z_to_bv 8 0) -> i < z -> z - i <= Z.of_nat k ->
  evt rsegs (lws_post ra sp gp tp t0 t1 t2 s0 s1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (B + i + 1)) (Z_to_bv 64 VCT_ADDR) (Z_to_bv 64 (bv_unsigned b)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x1b420) fc None m (seg_rom rsegs)).
Proof.
  induction k as [|k IH]; intros until b; intros U8 MI Hn Hi Hb Hz IZ ZK; [exfalso; lia|].
  pose proof (u8arr_bound _ _ _ _ U8) as BB. pose proof (nth_error_lt _ _ _ Hz) as LZ.
  pose proof (byte_range b) as RB.
  pose proof (munch_refl [] m) as MU. pose proof (wmono_refl rsegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep.
  rewrite (Z.shiftl_mul_pow2 (bv_unsigned b) 1) by lia. change (2 ^ 1) with 2.
  pose proof (vct_read0 m (bv_unsigned b) (Z_to_bv 64 (VCT_ADDR + bv_unsigned b * 2)) MI RB ltac:(unfold wa; f_equal; lia)) as RD.
  zstep. clear RD.
  pose proof (vct_range (bv_unsigned b)) as VR.
  unfold zx16. rewrite (unsigned_lit (vct (bv_unsigned b))) by lia. rewrite (Z.mod_small (vct (bv_unsigned b)) (2 ^ 16)) by lia.
  (* [comment removed for export] *)
  zstep. zstep. if_cases KL; zify_cond KL.
  - (* [comment removed for export] *)
    apply evt_done. unfold lws_post. do 3 eexists. split; [reflexivity| left; reflexivity].
  - (* [comment removed for export] *)
    destruct (nth_error bs (Z.to_nat (i + 1))) as [b'|] eqn:Hn'; [| apply nth_error_None in Hn'; exfalso; lia].
    pose proof (byte_range b') as RB'.
    pose proof (u8arr_read rsegs m B bs (i + 1) b' (Z_to_bv 64 (B + i + 1)) U8 Hn' ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    zstep. clear RD. zstep. zstep. if_cases KZ; zify_cond KZ.
    + (* [comment removed for export] *)
      replace (B + i + 2) with (B + (i + 1) + 1) by lia.
      assert (NZ : i + 1 <> z) by (intros E; rewrite E in Hn'; rewrite Hz in Hn'; injection Hn' as E'; rewrite <- E' in KZ; apply KZ; reflexivity).
      eapply (IH _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m B bs (i + 1) z b'); [exact U8 | exact MI | exact Hn' | lia | exact KZ | exact Hz | lia | lia].
    + (* [comment removed for export] *)
      apply evt_done. unfold lws_post. do 3 eexists. split; [reflexivity| right; reflexivity].
Qed.

(* [comment removed for export] *)
Ltac flat_addr base n :=
  lazymatch base with
  | (?b0 + ?k)%Z => let v := eval lazy in (k + n)%Z in constr:((b0 + v)%Z)
  | _ => constr:((base + n)%Z)
  end.

Ltac vep_split3 VEPC k VA VP VB :=
  lazymatch type of VEPC with rw_cells ?segs ?mx ?base ?cs =>
    let cs1 := eval lazy beta iota delta [firstn] in (firstn k cs) in
    let rest := eval lazy beta iota delta [skipn] in (skipn k cs) in
    lazymatch rest with ?c :: ?cs2 =>
      let n1 := eval lazy in (Z.of_nat (cells_size cs1)) in
      let n2 := eval lazy in (n1 + Z.of_nat (csize c))%Z in
      let t1 := flat_addr base n1 in
      let t2 := flat_addr base n2 in
      change cs with (cs1 ++ (c :: cs2)) in VEPC;
      apply (proj1 (rw_cells_app segs mx base cs1 (c :: cs2))) in VEPC;
      destruct VEPC as [VA VP];
      change (c :: cs2) with ([c] ++ cs2) in VP;
      apply (proj1 (rw_cells_app segs mx _ [c] cs2)) in VP;
      destruct VP as [VP VB];
      apply (rwc_eq segs mx _ t1) in VP; [| cbn; lia];
      apply (rwc_eq segs mx _ t2) in VB; [| cbn; lia]
    end
  end.

Ltac vep_join3 VA VP VB VEPC :=
  lazymatch type of VA with rw_cells ?segs ?mx ?base ?cs1 =>
  lazymatch type of VP with rw_cells _ _ ?a1 [?c] =>
  lazymatch type of VB with rw_cells _ _ ?a2 ?cs2 =>
    let n1 := eval lazy in (Z.of_nat (cells_size cs1)) in
    let H1 := fresh in let H2 := fresh in
    assert (H2 : rw_cells segs mx (base + n1 + Z.of_nat (cells_size [c])) cs2) by (eapply rwc_eq; [exact VB | cbn; lia]);
    assert (H1 : rw_cells segs mx (base + Z.of_nat (cells_size cs1)) ([c] ++ cs2))
      by (apply (proj2 (rw_cells_app segs mx _ [c] cs2)); split; [eapply rwc_eq; [exact VP | cbn; lia] | exact H2]);
    pose proof (proj2 (rw_cells_app segs mx base cs1 ([c] ++ cs2)) (conj VA H1)) as VEPC;
    cbn [app] in VEPC; clear VA VP VB H1 H2
  end end end.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Variables (VEP : Z) (v : vep) (tag : list byte) (q : vep_pads) (ya : vsb_rec) (vi : option vsb_rec) (H : henv) (lo : Z).
  Variables (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
            (m : mem) (md : Model) (A : AS) (T : TSet).
  Hypothesis AINV : ainv A m md.
  Hypothesis MI : mem_inv rsegs m.
  Hypothesis A0 : a0 = Z_to_bv 64 VEP.
  Hypothesis A1 : a1 = Z_to_bv 64 0.
  Hypothesis VOBJ : vep_obj LayoutP0 A m VEP v tag q.
  Hypothesis VBASE : vep_base H VEP v.
  Hypothesis HENV : henv_ok LayoutP0 VI0 H m.
  Hypothesis HG : henv_geom H.
  Hypothesis IMG : img_ok0 m.
  Hypothesis HMH : v Fmatch_hit = vi_tbl_attr_include VI0 \/ v Fmatch_hit = vi_tbl_attr_include VI0 + 16.
  Hypothesis HIC : bool01 (v Finclude_continue).
  Hypothesis ANZ : v Fattr_vsb <> 0.
  Hypothesis AOBJ : vsb_obj LayoutP0 A m (v Fattr_vsb) ya true.
  Hypothesis AERR : vb_error ya = 0.
  Hypothesis NAS : v Fattr_vsb <> VEP.
  Hypothesis NAB : vb_buf ya <> VEP.
  Hypothesis HVI : match vi with
      | None => v Finclude_src = 0
      | Some yi => v Finclude_src <> 0 /\ vsb_obj LayoutP0 A m (v Finclude_src) yi true /\ vb_error yi = 0 /\
                   v Finclude_src <> VEP /\ vb_buf yi <> VEP /\ v Finclude_src <> v Fattr_vsb /\ v Finclude_src <> vb_buf ya /\
                   vb_buf yi <> v Fattr_vsb /\ vb_buf yi <> vb_buf ya
      end.
  Hypothesis TP : tp = al_tp LayoutP0.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis RA2 : bv_unsigned ra mod 2 = 0.
  Hypothesis ST : stk rsegs m lo (bv_unsigned sp).
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + DOINCL_STACK <= bv_unsigned sp.
  Hypothesis SPH : bv_unsigned sp <= h_sp H.
  Hypothesis K : forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A' : AS) (m' : mem) (md' : Model)
              (v' : vep) (vi' : option vsb_rec),
          ainv A' m' md' -> mem_inv rsegs m' -> md_frame md md' ->
          stk rsegs m' lo (bv_unsigned sp) -> henv_ok LayoutP0 VI0 H m' ->
          vep_obj LayoutP0 A' m' VEP v' tag q ->
          (  (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0 /\ vi' = Some ya /\
                        (forall r, a_live A' r = a_live A r) /\ a_livebytes A' = a_livebytes A /\ a_nlive A' = a_nlive A)
          \/ (* [comment removed for export] *) (vi <> None /\ v' = fupd (fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0) Finclude_src 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        (match vi with Some yi => a_live A' (v Finclude_src) = None /\ a_live A' (vb_buf yi) = None /\
                                                  a_livebytes A' = a_livebytes A - 80 - vb_size ya - vb_size yi /\ a_nlive A' = a_nlive A - 4
                                     | None => False end) /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> r <> v Finclude_src ->
                                   r <> match vi with Some yi => vb_buf yi | None => 0 end -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (vi = None /\ v' = fupd (fupd v Fstate (vi_st VI0 S_TagError)) Fattr_vsb 0 /\ vi' = None /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))
          \/ (* [comment removed for export] *) (exists ic, bool01 ic /\ v' = fupd (fupd v Finclude_continue ic) Fattr_vsb 0 /\ vi' = vi /\
                        a_live A' (v Fattr_vsb) = None /\ a_live A' (vb_buf ya) = None /\
                        a_livebytes A' = a_livebytes A - 40 - vb_size ya /\ a_nlive A' = a_nlive A - 2 /\
                        (forall r, r <> v Fattr_vsb -> r <> vb_buf ya -> a_live A' r = a_live A r))) ->
          match vi' with
          | None => v' Finclude_src = 0
          | Some yi => v' Finclude_src <> 0 /\ vsb_obj LayoutP0 A' m' (v' Finclude_src) yi true /\ vb_error yi = 0
          end ->
          cframe LayoutP0 (owned A) (owned A') (bv_unsigned sp) DOINCL_STACK
                 (fun a => blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a
                           \/ match vi with Some yi => vsb_blocks (v Finclude_src) yi a | None => False end
                           \/ (h_vsc H + 1304 <= a < h_vsc H + 1320))
                 nowhere m m' ->
          realizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7'
                                          s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                     bvmap_empty (ret_pc ra) (Z_to_bv 32 0) None m' (seg_rom rsegs)) md') T.

  (* [comment removed for export] *)
  Let W : list ivl := [(bv_unsigned sp - 8544, bv_unsigned sp); (h_vsc H + 1304, h_vsc H + 1320); (VEP, VEP + 312)].
  (* [comment removed for export] *)
  Let FRAME (j : list byte) : list cell :=
    [CB 8 j; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Local Ltac prelims :=
    pose proof (as_layout_order (L:=LayoutP0)) as LAY; cbn [al_image_lo al_rw_lo al_image_hi LayoutP0] in LAY;
    pose proof alloc_ceiling_val as ACV;
    pose proof HG as (G1 & G2 & G3); unfold HFRAME in G3;
    pose proof VBASE as (EVC & ECB & EPRIV & EDZ & EURL); cbn [vi_cb vi_url VI0] in ECB, EURL;
    unfold DOINCL_STACK, REALLOC_STACK, DESTROY_STACK, FREE_STACK in *;
    pose proof VOBJ as (VLV & VEPC0 & TAG & PADS); cbn [al_segs LayoutP0] in VEPC0;
    pose proof (as_live_ok A m md VEP _ AINV VLV) as (_ & V16 & Vlo & Vhi & Vimg & Vmap & Vown);
    unfold off_image in Vimg; cbn [al_image_lo al_image_hi LayoutP0] in Vimg;
    (first [ pose proof (PADS) as dR_1; dand7 dR_1 as P36 P124 P140 P196 P236 P268 P308 | pose proof PADS as (P36 & P124 & P140 & P196 & P236 & P268 & P308) ]);
    (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ)) as dR_2; dand11 dR_2 as SA16 SAlo SAhi SAimg BA16 BAlo BAhi BAimg DSBA SAmap BAmap | pose proof (vsb_obj_geom LayoutP0 A m md (v Fattr_vsb) ya true AINV AOBJ) as (SA16 & SAlo & SAhi & SAimg & BA16 & BAlo & BAhi & BAimg & DSBA & SAmap & BAmap) ]);
    pose proof (proj1 (proj2 (proj2 AOBJ))) as LSA; pose proof (proj1 (proj2 (proj2 (proj2 AOBJ)))) as LBA;
    pose proof (as_live_disjoint A m md VEP 312 (v Fattr_vsb) 40 AINV VLV LSA (not_eq_sym NAS)) as DVSA;
    pose proof (as_live_disjoint A m md VEP 312 (vb_buf ya) (vb_size ya) AINV VLV LBA (not_eq_sym NAB)) as DVBA;
    assert (Evc : h_vc H = h_sp H + 1304) by reflexivity;
    assert (Ewrk : h_wrk H = h_sp H + 1120) by reflexivity;
    assert (Evsc : h_vsc H = h_sp H + 2240) by reflexivity;
    assert (Ecp : h_cp H = h_sp H + 1488) by reflexivity.

  (* [comment removed for export] *)
  Local Ltac hide_disj := repeat match goal with H : _ \/ _ |- _ => hide H end.

  (* [comment removed for export] *)
  Local Ltac touch_all :=
    pose proof (conj AINV (conj MI (conj A0 (conj A1 (conj VOBJ (conj VBASE (conj HENV (conj HG (conj IMG (conj HMH (conj HIC
      (conj ANZ (conj AOBJ (conj AERR (conj NAS (conj NAB (conj HVI (conj TP (conj SP16 (conj RA2 (conj ST (conj CEIL (conj LO
      (conj SPH K)))))))))))))))))))))))) as ALL_HYPS; hide ALL_HYPS.

  (* [comment removed for export] *)
  Local Ltac xfer_piece CF H C :=
    lazymatch type of CF with cframe _ (owned ?Ax) (owned ?Ay) ?spv ?win ?V ?N ?ma ?mb =>
    lazymatch type of H with rw_cells _ _ ?a ?cs =>
      apply (rw_cells_ccall LayoutP0 Ax Ay spv win V N ma mb CF a cs) in H;
      [ | exact C
        | cbn [cells_size csize Nat.add length app];
          lazymatch goal with Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z |- _ =>
            split; [ clear - Vhi CEIL LO; lia
                   | intros i Hi X; unfold blk, nowhere in X; cbn beta in X;
                     repeat match goal with D : (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => revert D | D : kept (VEP + 312 <= _ \/ _ <= VEP)%Z |- _ => unhide D; revert D end;
                     clear - Hi X; intros; lia ] end ]
    end end.

  (* [comment removed for export] *)
  Local Ltac geo_lia :=
    try match goal with Vi : kept (VEP + 312 <= 65536 \/ _)%Z |- _ => unhide Vi end;
    lazymatch goal with
    | Vimg : (VEP + 312 <= 65536 \/ _)%Z, Vhi : (VEP + 312 <= alloc_ceiling)%Z, CEIL : (alloc_ceiling <= lo)%Z, LO : (lo + _ <= bv_unsigned sp)%Z,
      ACV : (_ <= alloc_ceiling <= _)%Z, G2 : (alloc_ceiling + 12720 <= h_sp H)%Z, SPH : (bv_unsigned sp <= h_sp H)%Z,
      Evsc : h_vsc H = _, Evc : h_vc H = _, Ewrk : h_wrk H = _, Ecp : h_cp H = _ |- _ =>
        clear - Vimg Vhi CEIL LO ACV G2 SPH Evsc Evc Ewrk Ecp; intros; lia
    end.

  (* [comment removed for export] *)
  Local Ltac env_at mq MU WM :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m, IMG : img_ok0 m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in
      (first [ pose proof (GLOB) as dR_3; dand4 dR_3 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP; cbn [vi_bss VI0] in EBSS; rewrite EBSS in BSS;
      eapply (rw_cells_transport rsegs _ m mq) in BSS; [| exact MU | exact WM | cbn; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in CP; [| exact MU | exact WM | cbn; unfold h_cp; geo_lia];
      let VC := fresh "VC" in let WK := fresh "WK" in
      let p1 := fresh "vcpad" in let r1 := fresh "vcrest" in let p2 := fresh "wkpad" in let r2 := fresh "wkrest" in
      let L1 := fresh "LP" in let L2 := fresh "LR" in let L3 := fresh "LP" in let L4 := fresh "LR" in
      (first [ pose proof (HOBJ) as dR_4; dand3 dR_4 as VC WK _ | pose proof HOBJ as (VC & WK & _) ]);
      (first [ dex2 VC as p1 r1; dand3 VC as L1 L2 VC | dand5 VC as p1 r1 L1 L2 VC | destruct VC as (p1 & r1 & L1 & L2 & VC) ]); (first [ dex2 WK as p2 r2; dand3 WK as L3 L4 WK | dand5 WK as p2 r2 L3 L4 WK | destruct WK as (p2 & r2 & L3 & L4 & WK) ]);
      cbn [al_segs LayoutP0] in VC, WK; unfold vc_cells in VC; unfold wrk_cells in WK;
      eapply (rw_cells_transport rsegs _ m mq) in VC; [| exact MU | exact WM | cbn; revert L1 L2; geo_lia];
      eapply (rw_cells_transport rsegs _ m mq) in WK; [| exact MU | exact WM | cbn; revert L3 L4; geo_lia];
      let GV := fresh "GVSC" in
      pose proof IMG as (_ & _ & GV & _); unfold GOT_vsc in GV;
      eapply (ro_cells_transport rsegs _ m mq) in GV; [| exact MU | cbn; geo_lia]
    end.

  (* [comment removed for export] *)
  Local Ltac henv_at mx MU WM CNT HENV0 :=
    lazymatch goal with GLOB : glob_ok _ _ H m, HOBJ : hobj_ok _ _ H m |- _ =>
      let EBSS := fresh "EBSS" in let BSS := fresh "BSS" in let CP := fresh "CP" in let c := fresh "cnt" in let C := fresh "CNT" in
      (first [ pose proof (GLOB) as dR_7; dand4 dR_7 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]); cbn [al_segs LayoutP0] in BSS, CP;
      destruct (rw_cells_forget _ _ _ _ CNT) as [c C]; cbn [cells_size csize Nat.add] in C;
      assert (HENV0 : henv_ok LayoutP0 VI0 H mx);
      [ split;
        [ eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact C];
          [ eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS; cbn; geo_lia]
          | eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; unfold h_cp; geo_lia] ]
        | eapply (hobj_ok_munch LayoutP0); [exact HOBJ | exact MU | exact WM |];
          let a := fresh "a" in let Ha := fresh "Ha" in
          intros a Ha; unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha; cbn [outside]; revert Ha; geo_lia ]
      | clear BSS CP C c EBSS ]
    end.

  (* [comment removed for export] *)
  Local Ltac hcover_destroy LS LB LV :=
    let a := fresh "a" in let X := fresh "X" in
    intros a [X|[X|X]];
    [ eexists _, _; split; [exact LS|] | eexists _, _; split; [exact LB|] | eexists _, _; split; [exact LV|] ];
    unfold blk in X; (split; [| clear - X; lia]);
    let E := fresh "E" in
    intros E; cbn in E; unhide_neqs;
    repeat match type of E with _ \/ _ => destruct E as [E|E] end; first [exact E | congruence].

  (* [comment removed for export] *)
  Local Ltac err_block STq :=
    do 15 zstep;
    (* [comment removed for export] *)
    zstep; carve_frame 48%nat STq; do 8 zstep;
    lazymatch goal with FR2 : rw_cells _ _ (bv_unsigned sp + -160)%Z _ |- _ =>
      release_frame FR2 STq (bv_unsigned sp + -112)%Z end.

  #[using="SPH LO CEIL NAB NAS AOBJ ANZ HG VBASE VOBJ AINV md m ra lo ya q tag v"] Lemma CFP : client_fp LayoutP0 A W.
  Proof.
    prelims. cbn. split; [left; lia|]. split; [left; lia|]. split; [right; left; exists VEP, 312; split; [exact VLV| lia]| exact I].
  Qed.

  (* [comment removed for export] *)
  #[using="NAB NAS AOBJ HG VBASE VOBJ AINV A md m q tag AI Clg"] Lemma W_cover : forall (P : Z -> Prop) a, 0 <= a < 2^64 -> ~ outside W a ->
    (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/
    (blk VEP 312 a \/ vsb_blocks (v Fattr_vsb) ya a \/ P a \/ (h_vsc H + 1304 <= a < h_vsc H + 1320)).
  Proof.
    prelims. intros P a Ha NO. cbn [outside W] in NO.
    assert (C3 : (bv_unsigned sp - 8544 <= a < bv_unsigned sp) \/ (h_vsc H + 1304 <= a < h_vsc H + 1320) \/ (VEP <= a < VEP + 312)) by (clear - NO; lia).
    clear NO. destruct C3 as [X|[X|X]]; [left; exact X | right; right; right; right; exact X | right; left; split; [clear - Vlo; lia| exact X]].
  Qed.

  (* [comment removed for export] *)
  Local Ltac accept_tail EVI :=
    do 19 zstep;
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia; try rewrite (Z_to_bv_bv_unsigned sp);
    cps_done;
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ =>
    lazymatch goal with FR : rw_cells _ mx (bv_unsigned sp + -112)%Z _, STq : stk _ mx lo _, MU : munch _ m mx, WM : wmono _ m mx,
                        VEPC : rw_cells _ mx VEP _, CNT : rw_cells _ mx (h_vsc H + 1304)%Z _,
                        MDL : m_vm_lazy md = [], MDH : m_halted md = None,
                        VLV : a_live A VEP = Some 312, TAG : length tag = 8%nat, PADS : vep_pads_wf q, EVC : v Fvc = h_vc H |- _ =>
      release_frame FR STq (bv_unsigned sp);
      let AINVf := fresh "AINVf" in let HENVf := fresh "HENVf" in
      pose proof (ainv_munch LayoutP0 A m mx md _ AINV MU WM CFP) as AINVf;
      henv_at mx MU WM CNT HENVf;
      unhide_neqs;
      eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A mx md (fupd (fupd v Finclude_src (v Fattr_vsb)) Fattr_vsb 0) (Some ya));
      [ exact AINVf | assumption | apply md_frame_refl; [exact MDL| exact MDH] | exact STq | exact HENVf
      | split; [exact VLV|]; split; [| split; [exact TAG| exact PADS]];
        cbn [al_segs LayoutP0]; unfold vep_cells; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; rewrite EVC; exact VEPC
      | left; split; [exact EVI|]; split; [reflexivity|]; split; [reflexivity|]; split; [intros r; reflexivity| split; reflexivity]
      | cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; split; [exact ANZ|]; split; [| exact AERR];
        eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | | ];
        [ cbn; lazymatch goal with D : kept (VEP + 312 <= v Fattr_vsb \/ _)%Z, B : (v Fattr_vsb + 40 <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end
        | cbn; lazymatch goal with D : kept (VEP + 312 <= vb_buf ya \/ _)%Z, B : (vb_buf ya + vb_size ya <= alloc_ceiling)%Z |- _ => unhide D; revert D B; geo_lia end ]
      | rewrite EVI; eapply (cframe_stores LayoutP0 _ _ _ _ m mx); [exact MU | apply W_cover | eapply (stk_mapped (L:=LayoutP0)); [exact STq | exact CEIL | clear -LO; lia | clear; lia]] ]
    end end.

  (* [comment removed for export] *)
  #[using="K SPH LO CEIL ST RA2 SP16 TP HVI NAB NAS AERR AOBJ ANZ HIC HMH IMG HG HENV VBASE VOBJ A1 A0 MI AINV A a1 a0 vi ya AI Clg"] Lemma seg_onerr : forall (xra xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7 xt0 xt1 xt2 xt3 xt4 xt5 xt6 : word) (mq : mem) (junk cnt : list byte),
    mem_inv rsegs mq -> stk rsegs mq lo (bv_unsigned sp + -112) ->
    rw_cells rsegs mq (bv_unsigned sp + -112) (FRAME junk) ->
    rw_cells rsegs mq VEP (vep_cells v tag q) ->
    rw_cells rsegs mq (h_vsc H + 1304) [CB 16 cnt] ->
    munch W m mq -> wmono rsegs m mq ->
    realizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -112)) gp tp xt0 xt1 xt2 (Z_to_bv 64 VEP) xs1 xa0 xa1 xa2 xa3 xa4 xa5 xa6 xa7
                                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 xt3 xt4 xt5 xt6)
                               bvmap_empty (Z_to_bv 64 0x1b164) (Z_to_bv 32 0) None mq (seg_rom rsegs)) md) T.
  Proof.
    touch_all.
    intros until cnt. intros MIq STq FR VEPC CNT MU WM.
    pose proof (as_lazy_nil A m md AINV) as [MDL MDH]. prelims. clear VEPC0. cbv delta [W] in MU. cbv delta [FRAME] in FR.
    unfold vep_cells in VEPC.
    (* [comment removed for export] *)
    assert (AOBJq : vsb_obj LayoutP0 A mq (v Fattr_vsb) ya true)
      by (eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | cbn; clear - DVSA SAhi CEIL LO ACV G2 SPH Evsc; try unhide DVSA; lia | cbn; clear - DVBA BAhi CEIL LO ACV G2 SPH Evsc; try unhide DVBA; lia]).
    pose proof AOBJq as AO. vsb_open AO. (first [ dex1 VBUF as bs; dand3 VBUF as U8 LBS NUL | dand4 VBUF as bs U8 LBS NUL | destruct VBUF as (bs & U8 & LBS & NUL) ]). cbn [al_segs LayoutP0] in U8.
    (first [ pose proof (VINV) as dR_9; dand8 dR_9 as Vsz Vlen Verr Vind Vfl Vb0 Vb47 Vbm | pose proof VINV as (Vsz & Vlen & Verr & Vind & Vfl & Vb0 & Vb47 & Vbm) ]).
    hide MI. hide ST. clear HMH Verr. hide_disj. hide_slow.
    apply rz_go; [exact MDH | exact MDL |].
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    call_fr (VSB_data_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ mq (v Fattr_vsb) ya lo) by
      (idtac; [> reflexivity | exact VSBC | exact VINV | exact SAlo | exact SAhi
              | rewrite unsigned_lit by lia; exact STq | rewrite unsigned_lit by lia; lia | exact CEIL
              | rewrite unsigned_lit by lia; lia | exact MIq ]).
    lazymatch goal with S : stk _ ?mq lo _ |- evt _ _ (MS _ _ _ _ _ ?mq _) => rename S into STq end.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep.
    destruct (strcmp_walk_nul_l STR_continue bs 8 eq_refl ltac:(lia)) as [rc WRC].
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      eapply evt_cut; [eapply strcmp_spec with (ls := STR_continue) (rs := bs) (v := rc);
        [ rewrite unsigned_lit by lia; apply str_continue_at; assumption
        | rewrite unsigned_lit by lia; exact (proj1 U8)
        | exact WRC | assumption ]
      | post_call_fr rsegs mq ] end.
    repeat match goal with Hb : bytes_at _ _ _ _ |- _ => clear Hb end.
    clear VSBC U8 VLS VLB VNE.
    (* [comment removed for export] *)
    zstep. zstep. zstep.
    set (ic := Z.b2z (rc mod 18446744073709551616 <? 1)) in *.
    assert (HIC' : bool01 ic) by (subst ic; destruct (rc mod 18446744073709551616 <? 1); cbv; [right|left]; reflexivity).
    (* [comment removed for export] *)
    do 16 zstep.
    try replace (bv_unsigned sp + -112 + 112) with (bv_unsigned sp) by lia. try rewrite (Z_to_bv_bv_unsigned sp).
    apply rz_stop.
    lazymatch goal with |- realizes _ (mkCfg (MS _ _ _ _ _ ?mx _) _) _ => rename mx into m0 end.
    release_frame FR STq (bv_unsigned sp).
    pose proof (ainv_munch LayoutP0 A m m0 md _ AINV MU WM CFP) as AINV0.
    assert (AOBJ0 : vsb_obj LayoutP0 A m0 (v Fattr_vsb) ya true)
      by (eapply (vsb_obj_munch LayoutP0); [exact AOBJ | exact MU | exact WM | cbn; clear - DVSA SAhi CEIL LO ACV G2 SPH Evsc; try unhide DVSA; lia | cbn; clear - DVBA BAhi CEIL LO ACV G2 SPH Evsc; try unhide DVBA; lia]).
    vep_split3 VEPC 36%nat VEPa VEPp VEPb.
    pose proof (crange_block (L:=LayoutP0) A m0 md VEP 312 VEP 224 AINV0 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRa.
    pose proof (crange_block (L:=LayoutP0) A m0 md VEP 312 (VEP + 232) 80 AINV0 VLV ltac:(lia) ltac:(lia) ltac:(lia)) as CRb.
    (* [comment removed for export] *)
    destruct HENV as [GLOB HOBJ]. (first [ pose proof (GLOB) as dR_10; dand4 dR_10 as EBSS BSS CP _ | pose proof GLOB as (EBSS & BSS & CP & _) ]). cbn [al_segs LayoutP0] in BSS, CP.
    pose proof EBSS as EBSS'. cbn [vi_bss VI0] in EBSS'.
    assert (HENV0 : henv_ok LayoutP0 VI0 H m0).
    { split.
      - eapply (glob_ok_intro LayoutP0); [exact EBSS | | | exact CNT].
        + eapply rw_cells_transport; [exact BSS | exact MU | exact WM | rewrite EBSS'; cbn; clear - Vimg CEIL LO ACV G2 SPH Evsc; try unhide Vimg; lia].
        + eapply rw_cells_transport; [exact CP | exact MU | exact WM | cbn; clear - Vhi CEIL LO ACV G2 SPH Evsc Ecp; lia].
      - eapply (hobj_ok_munch LayoutP0); [exact HOBJ | exact MU | exact WM |].
        intros a Ha. unfold h_vc, h_wrk, h_req, h_resp, h_hd in Ha. cbn [outside]. clear - Ha Vhi CEIL LO ACV G2 SPH Evsc. lia. }
    clear BSS CP CNT.
    unfold VSB_destroy_entry.
    eapply (VSB_destroy_cps _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ m0 md A (VEP + 224) (v Fattr_vsb) ya true lo);
      [ exact AINV0 | assumption | reflexivity | cbn [w64]; exact VEPp
      | right; exists VEP, 312; split; [exact VLV|]; split; [unhide NAS; unhide NAB; intros [X|[X|[]]]; [exact (NAS X)| exact (NAB X)] | clear; lia]
      | exact AOBJ0 | exact TP | exact SP16 | exact RA2 | exact STq | exact CEIL | unfold DESTROY_STACK, FREE_STACK; clear - LO; lia | clear - SPH G3; lia | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A2 m3 md3 AINV3 MI3 MDF3 ST3 PSC3 LVS3 LVB3 LIVE3 LB3 NL3 CF3.
    unfold DESTROY_STACK, FREE_STACK in CF3.
    assert (HC : hcover A [] (fun a => blk (v Fattr_vsb) 40 a \/ blk (vb_buf ya) (vb_size ya) a \/ VEP + 224 <= a < VEP + 224 + 8)).
    { intros a [X|[X|X]]; [exists (v Fattr_vsb), 40 | exists (vb_buf ya), (vb_size ya) | exists VEP, 312];
        (split; [assumption|]); (split; [intros []|]); unfold blk in X; clear - X; lia. }
    pose proof (henv_call H A A2 m0 m3 md (bv_unsigned sp) _ _ _ [] AINV0 CF3 HG ltac:(clear - CEIL LO; lia) SPH HC HENV0) as HENV3.
    xfer_piece CF3 VEPa CRa. xfer_piece CF3 VEPb CRb. try clear STq. try clear MIq.
    cbn [w64] in PSC3. vep_join3 VEPa PSC3 VEPb VEPC3.
    unhide_neqs.
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A2 m3 md3 (fupd (fupd v Finclude_continue ic) Fattr_vsb 0) vi);
      [ exact AINV3 | exact MI3 | exact MDF3 | exact ST3 | exact HENV3 | | | | ].
    - (* [comment removed for export] *)
      split; [rewrite (LIVE3 VEP (not_eq_sym NAS) (not_eq_sym NAB)); exact VLV|].
      split; [| split; [exact TAG| exact PADS]].
      cbn [al_segs LayoutP0]. unfold vep_cells. cbn [fupd vf_beq vf_index N.eqb Pos.eqb]. exact VEPC3.
    - (* [comment removed for export] *)
      right; right; right. exists ic. split; [exact HIC'|]. split; [reflexivity|]. split; [reflexivity|].
      split; [exact LVS3|]. split; [exact LVB3|]. split; [exact LB3|]. split; [exact NL3|]. exact LIVE3.
    - (* [comment removed for export] *)
      destruct vi as [yi|]; cbn [fupd vf_beq vf_index N.eqb Pos.eqb]; [| exact HVI].
      destruct HVI as (INZ & IOBJ & IERR & NIS & NIB & NISA & NISB & NIBA & NIBB).
      (first [ pose proof ((vsb_obj_geom LayoutP0 A m md (v Finclude_src) yi true AINV IOBJ)) as dR_11; dand8 dR_11 as _ SIlo SIhi _ _ BIlo BIhi _ | pose proof (vsb_obj_geom LayoutP0 A m md (v Finclude_src) yi true AINV IOBJ) as (_ & SIlo & SIhi & _ & _ & BIlo & BIhi & _) ]).
      pose proof (proj1 (proj2 (proj2 IOBJ))) as LSI. pose proof (proj1 (proj2 (proj2 (proj2 IOBJ)))) as LBI.
      pose proof (as_live_disjoint A m md VEP 312 (v Finclude_src) 40 AINV VLV LSI (not_eq_sym NIS)) as DVSI.
      pose proof (as_live_disjoint A m md VEP 312 (vb_buf yi) (vb_size yi) AINV VLV LBI (not_eq_sym NIB)) as DVBI.
      split; [exact INZ|]. split; [| exact IERR].
      assert (IOBJ0 : vsb_obj LayoutP0 A m0 (v Finclude_src) yi true)
        by (eapply (vsb_obj_munch LayoutP0); [exact IOBJ | exact MU | exact WM | cbn; clear - DVSI SIhi CEIL LO ACV G2 SPH Evsc; try unhide DVSI; lia | cbn; clear - DVBI BIhi CEIL LO ACV G2 SPH Evsc; try unhide DVBI; lia]).
      eapply (vsb_obj_call H A A2 m0 m3 md (bv_unsigned sp) _ _ _ [v Finclude_src; vb_buf yi] AINV0 CF3 HG ltac:(clear - CEIL LO; lia));
        [ | left; reflexivity | right; left; reflexivity
        | rewrite (LIVE3 _ NISA NISB); exact LSI | rewrite (LIVE3 _ NIBA NIBB); exact LBI | exact IOBJ0 ].
      intros a [X|[X|X]]; left; [exists (v Fattr_vsb), 40 | exists (vb_buf ya), (vb_size ya) | exists VEP, 312];
        (split; [assumption|]); unfold blk in X;
        (split; [intros [E|[E|[]]]; clear - E NISA NISB NIBA NIBB NIS NIB; congruence | clear - X; lia]).
    - (* [comment removed for export] *)
      eapply (cframe_extend LayoutP0 _ _ (bv_unsigned sp) _ (bv_unsigned sp) _ _ _ _ _ m m0 m3 m3 _ []);
        [ exact MU | | exact CF3 | clear; lia | clear; lia | | intros a X; left; exact X | apply munch_refl
        | intros a _ X; exfalso; apply X; exact I
        | eapply (stk_mapped (L:=LayoutP0)); [exact ST3 | exact CEIL | clear -LO; lia | clear; lia] ].
      + apply W_cover.
      + intros a [X|[X|X]]; [right; left; left; exact X | right; left; right; exact X | left; split; [clear -Vlo; lia| clear -X; lia]].
  Qed.

End S.
