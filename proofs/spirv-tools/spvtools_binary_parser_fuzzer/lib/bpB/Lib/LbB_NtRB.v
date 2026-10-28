(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib HRep HRepFacts HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsStack0 BsWalk BXXRep RtB_Iface LibIface FPSteps.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv LbB_SR LbB_Own LbB_MILB
  LbB_PrsStmt LbB_ContStmt LbB_HEmpStmt LbB_HKit LbB_VecT LbB_NtStmt LbB_NtK LbB_NtRK LbB_NtD LbB_NtI LbB_NtI4 LbB_NtRL LbB_NtRE.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require LbB_HFind LbB_TopKit LbB_HEmpD LbB_HEmpI LbB_HEmpS LbB_HEmpR LbB_HEmpI3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HWord.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition R_NEWRET : Z := 0xf55c0.
Definition R_DRET : Z := 0xf5618.
Definition R_JN : Z := 0xf5628.

Lemma chain_keep {HCEIL : HeapCeil} (H : asr) : asan_rt_hyps H -> forall m m' cur CH (S1 : Z),
  as_chain H m cur CH -> (forall fp ra, In (fp, ra) CH -> S1 + 688 <= fp) ->
  (forall a, S1 + 672 <= a < 2 ^ 64 -> m' (wa a) = m (wa a)) -> as_chain H m' cur CH.
Proof.
  intros HH m m' cur CH S1 C F E. apply (ah_chain_ext H HH m m' cur CH C).
  intros fp ra a Hin Ha. pose proof (F fp ra Hin) as K. pose proof (ah_chain_range H HH m cur CH fp ra C Hin) as (R1 & _).
  apply E. lia.
Qed.

Ltac nrmJ HX := rewrite ?w_remu by lia; rewrite ?HX; rewrite ?w_mul by lia; rewrite ?w_add by lia; rewrite ?v_addi_Z by lia.
Ltac sc_brJ HX := cbn [sc_denot]; evs; cbn [edenot]; nrmJ HX; rewrite ?br_eq, ?br_ne, ?br_ltu, ?br_geu by lia; bool_lia.
Ltac kshadow_tacJ HX :=
  lazymatch goal with
  | |- kentry_ok _ ?E ?M (KWord (SA (EAlu ALU_SRL ?e (ELit 3)) _) 1 (ELit 0)) =>
      eapply kshadow0; [evs; cbn [edenot]; nrmJ HX; reflexivity | lia | sh0_from_gz]
  end.
Ltac sc_soJ HX WR := eapply (sc_storeok_wr _ _ _ _ _ _ _ WR); [evs; cbn [edenot]; nrmJ HX; first [reflexivity | f_equal; lia] | lia | cbn; lia | lia | cbn; lia].
Ltac rwc_newJ HX Hlf WR :=
  lazymatch goal with |- rw_cells _ (mem_denot ?E ?m ?lg) ?A [?c] =>
    let rec go pre post :=
      lazymatch post with
      | SE ?a ?w ?v :: ?post' =>
          first [ eapply (rw_cells_mem_denot_w E m pre a w v post' A c);
                  [ exact Hlf
                  | repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [edenot a_off a_base]; nrmJ HX; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia|]); apply Forall_nil
                  | unfold estart; evs; cbn [edenot a_off a_base]; nrmJ HX; rewrite ?u64_of_Z by lia; cbn [a_off a_base Z.of_nat]; lia
                  | exact WR | reflexivity | exact I | evs; cbn [edenot cbytes]; rewrite ?w_add, ?w_addm, ?v_addi_Z by lia; reflexivity ]
                | let pre' := eval cbn [app] in (pre ++ [SE a w v]) in go pre' post' ]
      end in
    go (@nil sentry) lg
  end.

Definition R_ZL : Z := 0xf566c.
Definition srZ : list expr := srs sr_id [(11%bv, EVar 35); (12%bv, EVar 34); (13%bv, EVar 36); (14%bv, EVar 32);
  (16%bv, ELit SHBASE); (27%bv, EVar 33)].
Definition KNZ : list kentry := [KRange (EVar 33) 1 (2 ^ 28); KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 34) 0 (2 ^ 28);
  KRange (EVar 35) 0 (2 ^ 31)].
Definition keptZ : list reg := [1; 2; 3; 4; 5; 6; 7; 8; 9; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 28; 29; 30; 31]%bv.
Lemma le8_zeroZ : le8 (Z_to_bv 64 0) = repeat (b8 0) 8.
Proof. vm_compute. reflexivity. Qed.

Section NtZ.
  Context {HCEIL : HeapCeil}.
  Variables (F : bvmap 5 word) (fc : bv 32) (p nn : Z).
  #[local] Notation st R pc M := (@PropExec.mkst (PropExec.mkFP F fc) R (Z_to_bv 64 pc) M (seg_rom asegs)).
  Hypothesis Hnn : 1 <= nn /\ 8 * nn <= 2 ^ 28.
  Hypothesis Hp : 1 <= p /\ p + 8 * nn <= 2 ^ 47.
  Hypothesis Happ : aapp p (8 * nn).

  Lemma zl_run : forall (k : nat) (i : Z) (R : bvmap 5 word) (M : mem),
    Z.of_nat k = nn - i -> 0 <= i < nn ->
    getr R 27%bv = Z_to_bv 64 nn -> getr R 12%bv = Z_to_bv 64 i -> getr R 11%bv = Z_to_bv 64 (8 * i) ->
    getr R 13%bv = Z_to_bv 64 (2 ^ 64 - 1 - p) -> getr R 14%bv = Z_to_bv 64 p -> getr R 16%bv = Z_to_bv 64 SHBASE ->
    wr_at asegs M (p + 8 * i) (8 * (nn - i)) -> addressable M p (8 * nn) ->
    exists R' M', CatSim.msteps asegs (st R R_ZL M) (st R' R_MS M')
      /\ (forall r, In r keptZ -> getr R' r = getr R r)
      /\ getr R' 27%bv = Z_to_bv 64 nn /\ getr R' 13%bv = Z_to_bv 64 (2 ^ 64 - 1 - p) /\ getr R' 14%bv = Z_to_bv 64 p
      /\ getr R' 16%bv = Z_to_bv 64 SHBASE
      /\ munch [(p + 8 * i, p + 8 * nn)] M M' /\ wmono asegs M M'
      /\ bytes_at asegs M' (p + 8 * i) (repeat (b8 0) (Z.to_nat (8 * (nn - i)))).
  Proof.
    pose proof Happ as HA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in HA.
    induction k as [|k IH]; intros i R M Hk Hi H27 H12 H11 H13 H14 H16 WR AD; [lia|].
    assert (GZ : gz M p (8 * nn)) by (apply LbB_HEmpI.gzA; [exact AD | rewrite Z.mul_comm, Z_mod_mult; reflexivity]).
    set (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 nn; Z_to_bv 64 i; Z_to_bv 64 (8 * i); Z_to_bv 64 (2 ^ 64 - 1 - p)]).
    assert (HR : regs_ok E srZ R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst E; evs; cbn [edenot]; rewrite ?w_add by lia; first [assumption | reflexivity]] |]).
      apply Forall_nil. }
    destruct (Z.eq_dec (i + 1) nn) as [Hl | Hm].
    - assert (HK : know_ok asegs E M (kn_fix 20 [R_ZL; R_MS] (SCR [true; false] [] []) R_ZL srZ KNZ 50)).
      { kn_eval. unfold know_ok.
        repeat (apply Forall_cons; [first [kshadow_tacJ H27 | cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia] |]). apply Forall_nil. }
      xrun_at (PropExec.mkFP F fc) asegs R R_ZL M (seg_rom asegs) HR HK 40%nat [R_ZL; R_MS] (SCR [true; false] [] []) 50%N.
      { split_scs; first [ sc_brJ H27 | sc_soJ H27 WR ]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
      assert (C0 : rw_cells asegs M1 (p + 8 * i) [C8 (Z_to_bv 64 0)]).
      { subst M1. rwc_newJ H27 Hlf (LbB_HEmpD.wr_at_subE M (p + 8 * i) (8 * (nn - i)) (p + 8 * i) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)). }
      exists R', M1. split; [exact Hms|].
      split; [exact (syms_id_sound R _ _ R' keptZ HR' eq_refl)|].
      split; [rreg HR' 27%bv X27; exact X27|]. split; [rreg HR' 13%bv X13; exact X13|].
      split; [rreg HR' 14%bv X14; exact X14|]. split; [rreg HR' 16%bv X16; exact X16|].
      split.
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [edenot a_off a_base]; rewrite ?w_add, ?v_addi_Z by lia;
                                    rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
        apply Forall_nil. }
      split; [subst M1; apply wmono_mem_denot|].
      destruct C0 as [[_ C0] _]. cbn [cells_bytes cbytes] in C0. rewrite app_nil_r, le8_zeroZ in C0.
      replace (Z.to_nat (8 * (nn - i))) with 8%nat by lia. exact C0.
    - assert (HK : know_ok asegs E M (kn_fix 20 [R_ZL; R_MS] (SCR [true; true] [] []) R_ZL srZ KNZ 50)).
      { kn_eval. unfold know_ok.
        repeat (apply Forall_cons; [first [kshadow_tacJ H27 | cbn [kentry_ok]; subst E; evs; rewrite u64_of_Z by lia; lia] |]). apply Forall_nil. }
      xrun_at (PropExec.mkFP F fc) asegs R R_ZL M (seg_rom asegs) HR HK 40%nat [R_ZL; R_MS] (SCR [true; true] [] []) 50%N.
      { split_scs; first [ sc_brJ H27 | sc_soJ H27 WR ]. }
      lazymatch type of Hlf with log_flat _ ?lg =>
        lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
          change mm with (mem_denot E M lg) in Hms; set (M1 := mem_denot E M lg) in Hms end end.
      rreg HR' 27%bv X27. rreg HR' 12%bv X12. rreg HR' 11%bv X11. rreg HR' 13%bv X13. rreg HR' 14%bv X14. rreg HR' 16%bv X16.
      rewrite ?w_add in X12 by lia. rewrite ?w_add in X11 by lia.
      assert (C0 : rw_cells asegs M1 (p + 8 * i) [C8 (Z_to_bv 64 0)]).
      { subst M1. rwc_newJ H27 Hlf (LbB_HEmpD.wr_at_subE M (p + 8 * i) (8 * (nn - i)) (p + 8 * i) 8 WR ltac:(lia) ltac:(lia) ltac:(lia)). }
      assert (MU1 : munch [(p + 8 * i, p + 8 * i + 8)] M M1).
      { subst M1. apply munch_mem_denot; [exact Hlf|].
        repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; cbn [edenot a_off a_base]; rewrite ?w_add, ?v_addi_Z by lia;
                                    rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
        apply Forall_nil. }
      assert (WM1 : wmono asegs M M1) by (subst M1; apply wmono_mem_denot).
      assert (AD1 : addressable M1 p (8 * nn)).
      { eapply addressable_transport; [exact AD | exact MU1 | exact WM1 | apply LbB_HEmpI.dsh_app; [| lia | lia | lia]].
        apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO; lia | apply Forall_nil]. }
      destruct (IH (i + 1) R' M1) as (R2 & M2 & Hms2 & K2 & Y27 & Y13 & Y14 & Y16 & MU2 & WM2 & B2);
        [lia | lia | exact X27 | rewrite X12; f_equal; lia | rewrite X11; f_equal; lia | exact X13 | exact X14 | exact X16 | | exact AD1 |].
      { eapply LbB_HEmpD.wr_at_subE; [exact (wr_at_wmono _ _ _ _ WR WM1) | lia | lia | lia]. }
      exists R2, M2. split; [eapply CatSim.msteps_trans; [exact Hms | exact Hms2]|].
      split; [intros r Hr; rewrite (K2 r Hr); exact (syms_id_sound R _ _ R' keptZ HR' eq_refl r Hr)|].
      split; [exact Y27|]. split; [exact Y13|]. split; [exact Y14|]. split; [exact Y16|].
      split.
      { apply (munch_trans _ M M1 M2).
        - apply (munch_weaken [(p + 8 * i, p + 8 * i + 8)]); [|exact MU1].
          intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I].
        - apply (munch_weaken [(p + 8 * (i + 1), p + 8 * nn)]); [|exact MU2].
          intros x Hx. cbn [outside] in *. destruct Hx as [Hx _]. split; [lia | exact I]. }
      split; [eapply wmono_trans; [exact WM1 | exact WM2]|].
      assert (C2 : rw_cells asegs M2 (p + 8 * i) [C8 (Z_to_bv 64 0)]).
      { eapply rw_cells_transport; [exact C0 | exact MU2 | exact WM2 | cbn [disjoint_from cells_size csize Z.of_nat]; lia]. }
      destruct C2 as [[_ C2] _]. cbn [cells_bytes cbytes] in C2. rewrite app_nil_r, le8_zeroZ in C2.
      replace (Z.to_nat (8 * (nn - i))) with (8 + Z.to_nat (8 * (nn - (i + 1))))%nat by lia.
      rewrite repeat_app. apply bytes_at_app. split; [exact C2|].
      rewrite repeat_length. replace (p + 8 * i + Z.of_nat 8) with (p + 8 * (i + 1)) by lia. exact B2.
  Qed.
End NtZ.

Definition srJ : list expr := srs sr_id [(2%bv, EVar 34); (9%bv, EVar 34); (13%bv, ELit 0);
  (21%bv, EAlu ALU_ADD (EAlu ALU_SRL (EVar 33) (ELit 3)) (ELit SHBASE)); (22%bv, EAlu ALU_ADD (EVar 33) (ELit 8));
  (25%bv, EVar 33); (26%bv, EAlu ALU_ADD (EVar 33) (ELit 24)); (27%bv, EVar 35)].
Definition KNJ : list kentry := [KRange (EVar 33) 1 (2 ^ 47); KRange (EVar 32) 1 (2 ^ 47); KRange (EVar 34) 1 (2 ^ 47);
  KRange (EVar 35) 1 (2 ^ 28); KWr (SA (EVar 33) 8) (ELit 8)].
Definition SCJ : scripts := SCR [true] [EAlu ALU_ADD (EAlu ALU_SRL (EAlu ALU_ADD (EVar 33) (ELit 8)) (ELit 3)) (ELit SHBASE); EVar 32; ELit SHBASE] [].
Lemma sh_wordJ : forall x, 0 <= x < 2 ^ 64 ->
  alu64 ALU_ADD (alu64 ALU_SRL (Z_to_bv 64 x) (Z_to_bv 64 3)) (Z_to_bv 64 2147450880) = Z_to_bv 64 (x / 8 + SHBASE).
Proof.
  intros x Hx. rewrite HWord.w_srl by lia. change (2 ^ 3) with 8.
  assert (0 <= x / 8 < 2 ^ 61) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  unfold SHBASE. rewrite w_add by lia. reflexivity.
Qed.
Lemma w_notpJ : forall p, 0 <= p < 2 ^ 64 ->
  alu64 ALU_ADD (mul_div M_MUL (Z_to_bv 64 (-1)) (Z_to_bv 64 p)) (Z_to_bv 64 (-1)) = Z_to_bv 64 (2 ^ 64 - 1 - p).
Proof.
  intros p Hp. apply bv_eq. cbn [alu64 alu mul_div].
  rewrite bv_add_unsigned, bv_mul_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod.
  rewrite (Z.mod_small p) by lia.
  replace ((-1) mod 2 ^ 64) with (2 ^ 64 - 1) by reflexivity.
  rewrite Zplus_mod_idemp_l.
  replace ((2 ^ 64 - 1) * p + (2 ^ 64 - 1)) with ((2 ^ 64 - 1 - p) + p * 2 ^ 64) by ring.
  rewrite Z.mod_add by lia. reflexivity.
Qed.
Lemma land7J : forall k, Z.land k 7 = k mod 8.
Proof. intros k. change 7 with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Section NtRB.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HHB : asan_rt_hyps_bp H.
  Let HH : asan_rt_hyps H := rt_bp_base H HHB.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.
  Variables (gp tp s0 s4 ty wd enc : word) (S1 : Z).
  Variables (sk0 : as_St H) (LB0 : list block) (LF : list fframe) (obj key v408 v576 v624 : Z) (ents : list ent).
  Variables (bl bc lo B shi : Z) (m0 : mem) (mo0 : Model).
  Variables (LBe : list block).
  Variable (CH : list (Z * Z)).
  #[local] Notation n := (bseq_next bc).
  #[local] Notation addr := (HRehashModel.addr (Z * Z * Z)).

  Hypothesis U0 : umapx MI_A 32 (nval32 ASEGS) (lbl LBe) m0 obj bl bc ents.
  Hypothesis Hlast : bc <> BSEQ_LAST.
  Hypothesis AL0 : ICM (8 * n) <= as_AL H sk0.
  Hypothesis OCE : obj + 40 <= aceil.
  Hypothesis LFO : map_live_frame LF obj.
  Hypothesis ACL : aceil <= lo.
  Hypothesis LOS : lo <= S1.
  Hypothesis LOR : lo <= S1 - ANT_STACK.
  Hypothesis TPV : tp = Z_to_bv 64 ATP.
  Hypothesis KR32 : 0 <= key < 2 ^ 32.
  Hypothesis ZLEN : Zlength ents + 1 < 2 ^ 24.
  Hypothesis SP16 : S1 mod 16 = 0.
  Hypothesis SPB : S1 + 672 <= B.
  Hypothesis BR : B < 2 ^ 64.
  Hypothesis TRK : trace_ok (as_TR H) APC0_FREE (R_DRET :: map snd CH).
  Hypothesis CHH : forall fp ra, In (fp, ra) CH -> S1 + 688 <= fp.
  #[local] Opaque bseq_next.
  Abbreviation QIx := (QI H gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0).

  Lemma stage_c : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y1 y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y19 y28 y29 : word) (errv : word) (LB' LBn : list block) (pid qn : bptr) (p pn : Z)
      (junk : list byte) (j584 : word),
    as_VIS H s msF = MS (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 (Z_to_bv 64 0) y14
                             y15 y16 y17 (Z_to_bv 64 key) y19 s4 (Z_to_bv 64 (obj / 8 + SHBASE)) (Z_to_bv 64 (obj + 8))
                             (Z_to_bv 64 pn) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29
                             (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)))
                        F (Z_to_bv 64 R_JN) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS ty enc S1 obj m j584 (Z_to_bv 64 (pn / 8 + SHBASE)) -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> (0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64) ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 32) -> agree_on m0 m (obj + 16) 24 ->
    cell8 ASEGS m obj p ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) junk] ->
    addressable m p (8 * n) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 32) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s LB' m -> Permutation LB' (LB0 ++ (pid, p, 8 * n) :: (qn, pn, 32) :: LBn) ->
    Permutation (lbl LBn) (map (fun e : ent => (addr e, 32)) ents) ->
    lb_own ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) m ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    rw_cells asegs m pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    addressable m pn 32 -> (bc = 0 \/ Zlength ents = bc) ->
    as_SR H QIx (mkCfg msF mo).
  Proof using HHB U0 Hlast OCE LFO ACL LOS TPV KR32 ZLEN.
    intros s msF mo m F fc y1 y5 y6 y7 y10 y11 y12 y14 y15 y16 y17 y19 y28 y29 errv LB' LBn pid qn p pn junk j584
      VIS FZ KR MP WS NS S1L S1H VR MI ST ERR RA NODES HDR Cbl PBLK ADP ADH ADN WRH RH PE PM OWN XP RF AC S0 AL CPN ADPN BCE.
    destruct (LbB_HEmpR.bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & _).
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U0)) as Hbc0.
    assert (Hn0 : 0 < n) by lia.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (OAPP & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof OAPP as HoA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in HoA.
    assert (INP : In (pid, p, 8 * n) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; left; reflexivity).
    pose proof (ah_blocks H HH _ _ _ _ RH INP) as (Hp0 & Hp16 & _ & HpI & HpC & HpF & HpA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hp0, Hp16, HpI, HpC, HpF, HpA. unfold AIMG_TOP in HpI.
    pose proof HpA as HpA'. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO in HpA'.
    assert (HXn : bv_unsigned (Z_to_bv 64 n) = n) by (apply u64_of_Z; lia).
    remember (mkR y1 (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) y10 y11 y12 (Z_to_bv 64 0) y14
                  y15 y16 y17 (Z_to_bv 64 key) y19 s4 (Z_to_bv 64 (obj / 8 + SHBASE)) (Z_to_bv 64 (obj + 8))
                  (Z_to_bv 64 pn) wd (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29
                  (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60))) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 p; Z_to_bv 64 obj; Z_to_bv 64 S1; Z_to_bv 64 n]).
    assert (HR : regs_ok E srJ R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; cbn [edenot];
        first [ reflexivity | rewrite w_add by lia; reflexivity | rewrite sh_wordJ by lia; reflexivity ]] |]).
      apply Forall_nil. }
    pose proof WS as (WS584 & WS600 & WS632 & WS656).
    pose proof NS as (NS408 & NS576 & NS616 & NS624 & NS648).
    assert (C664 : rw_cells asegs m (S1 + 664) [C8 (Z_to_bv 64 (sh (obj + 8)))]).
    { pose proof WS656 as C. change [C8 (Z_to_bv 64 obj); C8 (Z_to_bv 64 (sh (obj + 8)))]
        with ([C8 (Z_to_bv 64 obj)] ++ [C8 (Z_to_bv 64 (sh (obj + 8)))]) in C.
      apply rw_cells_app in C as [_ C]. cbn [cells_size csize Nat.add] in C.
      replace (S1 + 656 + Z.of_nat 8) with (S1 + 664) in C by lia. exact C. }
    assert (GZo : gz m obj 40) by (apply LbB_HEmpI.gzA; [exact ADH | reflexivity]).
    assert (HK : know_ok asegs E m (kn_fix 20 [R_ZL] SCJ R_JN srJ KNJ 50)).
    { kn_eval. unfold know_ok.
      repeat (apply Forall_cons; [first [ kshadow_tacJ HXn
                                        | cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho0 Ho1 Hn0 Hn28 Hp0 HpC HpI ACF1 ACF2 S1L S1H; lia
                                        | eapply (kwr_of_wr_at asegs E m obj 40); [exact WRH | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia] ] |]).
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R R_JN m (seg_rom asegs) HR HK 30%nat [R_ZL] SCJ 50%N.
    { split_scs.
      - cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [edenot a_base a_off]; rewrite ?u64_of_Z by lia.
        clear - OCE ACL LOS Ho0 Ho1 S1L S1H. lia.
      - eapply (sc_read_cellw _ _ _ _ _ _ _ _ (cellw8_of_rw_cells m (S1 + 616) SHBASE NS616 ltac:(unfold SHBASE; lia) ltac:(unfold SHBASE; lia))); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity].
      - cbn [sc_denot]; evs; cbn [edenot]. rewrite w_and by lia. rewrite land7J.
        replace (p mod 8) with 0 by (clear - Hp16; Z.div_mod_to_equations; lia). vm_compute. reflexivity.
      - eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbl); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity].
      - sc_shdj.
      - eapply (sc_read_cellw _ _ _ _ _ _ _ _ (cellw8_of_rw_cells m (S1 + 664) (sh (obj + 8)) C664 ltac:(unfold sh; rewrite ?ASHADOW_BASE_val; Z.div_mod_to_equations; lia) ltac:(unfold sh; rewrite ?ASHADOW_BASE_val; Z.div_mod_to_equations; lia))); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia |].
        evs; cbn [edenot]. rewrite w_add by lia. rewrite sh_wordJ by lia.
        f_equal. unfold sh. rewrite ?ASHADOW_BASE_val. unfold SHBASE. lia. }
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(obj + 8, obj + 16)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
    assert (Cbc1 : rw_cells asegs M1 (obj + 8) [C8 (Z_to_bv 64 n)]).
    { subst M1. rwc_new Hlf (LbB_HEmpD.wr_at_subE m obj 40 (obj + 8) 8 WRH ltac:(lia) ltac:(lia) ltac:(lia)). }
    destruct (LbB_HEmpD.obj_window_ok H HH LF obj LB' m (obj + 8) (obj + 16) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
    destruct (client_frame H HH s LB' LF B [(obj + 8, obj + 16)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m0 M1).
    { eapply (xpres_munch_mixed H HH s LB' LB0 ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) S1 (nt_X S1 obj) [(obj + 8, obj + 16)] m0 m M1);
        [exact XP | exact RH | exact PE | lia | exact MU1 | exact WM1 |].
      apply Forall_cons; [right; left; intros a Ha; cbn [rin_ivs nt_X Datatypes.fst Datatypes.snd] in *; left; lia | apply Forall_nil]. }
    assert (DSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(obj + 8, obj + 16)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk]. apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO; clear - HoA; lia | apply Forall_nil]. }
    assert (ADP1 : addressable M1 p (8 * n)) by (eapply addressable_transport; [exact ADP | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (ADH1 : addressable M1 obj 40) by (eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (ADN1 : forall e, In e ents -> addressable M1 (addr e) 32).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _). eapply addressable_transport; [exact (ADN e He) | exact MU1 | exact WM1 | apply DSH; lia]. }
    assert (INQ : In (qn, pn, 32) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; right; left; reflexivity).
    pose proof (ah_blocks H HH _ _ _ _ RH INQ) as (Hq0 & Hq16 & _ & HqI & HqC & HqF & HqA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hq0, Hq16, HqI, HqC, HqF, HqA. unfold AIMG_TOP in HqI.
    assert (HPO : apart p (8 * n) obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HpF OB1 OB2 Hn0; lia).
    assert (HQO : apart pn 32 obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HqF OB1 OB2; lia).
    assert (ADPN1 : addressable M1 pn 32) by (eapply addressable_transport; [exact ADPN | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (EA : errno_addr tp = ATP - 164) by (rewrite TPV; unfold errno_addr; rewrite u64_of_Z by (unfold ATP; lia); reflexivity).
    assert (TS : forall A cs, rw_cells asegs m A cs -> obj + 16 <= A \/ A + Z.of_nat (cells_size cs) <= obj + 8 -> rw_cells asegs M1 A cs).
    { intros A cs C D. eapply rw_cells_transport; [exact C | exact MU1 | exact WM1 | cbn [disjoint_from]; lia]. }
    assert (WS1 : WSLOTS ty enc S1 obj M1 j584 (Z_to_bv 64 (pn / 8 + SHBASE))).
    { split; [apply TS; [exact WS584 | cbn; lia]|]. split; [apply TS; [exact WS600 | cbn; lia]|].
      split; [apply TS; [exact WS632 | cbn; lia] | apply TS; [exact WS656 | cbn; lia]]. }
    assert (NS1 : nt_slots M1 S1 obj v408 v576 v624).
    { split; [apply TS; [exact NS408 | cbn; lia]|]. split; [apply TS; [exact NS576 | cbn; lia]|].
      split; [apply TS; [exact NS616 | cbn; lia]|]. split; [apply TS; [exact NS624 | cbn; lia] | apply TS; [exact NS648 | cbn; lia]]. }
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]) by (apply TS; [exact ERR | rewrite EA; cbn; clear - OB3; unfold ATP in *; lia]).
    assert (PBLK1 : rw_cells asegs M1 p [CB (Z.to_nat (8 * n)) junk])
      by (apply TS; [exact PBLK | cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HPO; unfold apart in HPO; lia]).
    assert (CPN1 : rw_cells asegs M1 pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
      by (apply TS; [exact CPN | cbn; clear - HQO; unfold apart in HQO; lia]).
    assert (NODES1 : forall e, In e ents -> agree_on m0 M1 (addr e) 32).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (u_node U0 (addr e) (fst (snd e)) (snd (snd e)) ltac:(destruct e as [q [k v]]; exact He)) as (_ & _ & _ & _ & _ & _ & _ & _ & Heo & _).
      eapply agree_on_trans; [exact (NODES e He)|]. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz Heo. unfold apart in Heo. lia. }
    assert (HDR1 : agree_on m0 M1 (obj + 16) 24).
    { eapply agree_on_trans; [exact HDR|]. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz. lia. }
    assert (Cbl1 : cell8 ASEGS M1 obj p).
    { eapply cellw_agree; [exact Cbl | | lia | cbn; lia]. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz. lia. }
    assert (OWN1 : lb_own ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) M1) by exact (lb_own_wmono _ _ _ OWN WM1).
    assert (WRH1 : wr_at asegs M1 obj 40) by exact (wr_at_wmono _ _ _ _ WRH WM1).
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 11%bv G11. rreg HR' 12%bv G12. rreg HR' 13%bv G13. rreg HR' 14%bv G14.
    rreg HR' 16%bv G16. rreg HR' 21%bv G21. rreg HR' 22%bv G22. rreg HR' 25%bv G25. rreg HR' 26%bv G26. rreg HR' 27%bv G27.
    rewrite ?w_add in G22, G26 by lia. rewrite sh_wordJ in G21 by lia. rewrite w_notpJ in G13 by lia.
    rewrite G2, G9, G11, G12, G13, G14, G16, G21, G22, G25, G26, G27 in HRe.
    destruct PBLK1 as [_ WRP1]. cbn [cells_size csize] in WRP1. rewrite Nat.add_0_r, Z2Nat.id in WRP1 by lia.
    destruct (zl_run F fc p n ltac:(lia) ltac:(lia) HpA (Z.to_nat n) 0 R' M1) as (R2 & M2 & Hzl & KZ & Y27 & Y13 & Y14 & Y16 & MU2 & WM2 & ZB2);
      [lia | lia | exact G27 | exact G12 | rewrite G11; reflexivity | exact G13 | exact G14 | exact G16
      | replace (p + 8 * 0) with p by lia; replace (8 * (n - 0)) with (8 * n) by lia; exact WRP1 | exact ADP1 |].
    rewrite Z.mul_0_r, Z.add_0_r in MU2. rewrite Z.mul_0_r, Z.add_0_r, Z.sub_0_r in ZB2.
    assert (Hms2 := CatSim.msteps_trans _ _ _ _ Hms Hzl).
    assert (Q : forall r v, In r keptZ -> getr R' r = v -> getr R2 r = v) by (intros r v Hr Hv; rewrite (KZ r Hr); exact Hv).
    eapply (sr_blk H HH); [exact KR | exact VIS | exact FHF | exact Hms2 |].
    intros msF1 mo1 KR1 MP1 VIS1.
    rewrite (Q 2%bv (Z_to_bv 64 S1) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 3%bv gp ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 4%bv tp ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 8%bv s0 ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 9%bv (Z_to_bv 64 S1) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 18%bv (Z_to_bv 64 key) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 20%bv s4 ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 23%bv (Z_to_bv 64 pn) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 24%bv wd ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 25%bv (Z_to_bv 64 obj) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 26%bv (Z_to_bv 64 (obj + 24)) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 30%bv (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite (Q 31%bv (Z_to_bv 64 (2 ^ 60)) ltac:(inb) ltac:(rewrite HRe; reflexivity)) in VIS1.
    rewrite Y27, Y13, Y14 in VIS1.
    assert (MI2 : mem_inv asegs M2) by exact (msteps_mem_inv asegs _ _ Hzl MI1).
    assert (ST2 : stk asegs M2 lo (S1 + 672)) by (eapply LbB_TopKit.stk_wmono; [exact ST1 | exact WM2 | clear - ACL ACF1; lia]).
    assert (ZER : rw_cells asegs M2 p [CB (Z.to_nat (8 * n)) (poison_bytes (Z.to_nat (8 * n)) 0)]).
    { split; [split|].
      - cbn [cells_wf cell_wf]. split; [unfold poison_bytes; apply repeat_length | exact I].
      - cbn [cells_bytes cbytes]. rewrite app_nil_r. unfold poison_bytes. exact ZB2.
      - cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. exact (wr_at_wmono _ _ _ _ WRP1 WM2). }
    destruct (LbB_HEmpI.blk_win H HH LF s LB' M1 pid p (8 * n) p (p + 8 * n) RH1 INP ltac:(lia) ltac:(lia)) as (P1 & P2 & P3 & P4 & P5).
    destruct (client_frame H HH s LB' LF B [(p, p + 8 * n)] M1 M2 RH1 RF1 AC1 RA1 MU2 WM2
               (Forall_cons _ _ _ P1 (Forall_nil _)) (Forall_cons _ _ _ P2 (Forall_nil _)) (Forall_cons _ _ _ P3 (Forall_nil _)))
      as (RH2 & RF2 & AC2 & RA2).
    assert (S02 : stack0 M2 lo shi) by (eapply stack0_transport; [exact S01 | exact MU2 | exact WM2 | exact (Forall_cons _ _ _ P4 (Forall_nil _))]).
    assert (XP2 : xpres H LB0 S1 (nt_X S1 obj) m0 M2).
    { eapply (xpres_munch_mixed H HH s LB' LB0 ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) S1 (nt_X S1 obj) _ m0 M1 M2);
        [exact XP1 | exact RH1 | exact PE | lia | exact MU2 | exact WM2 |].
      apply Forall_cons; [right; right; exists pid, p, (8 * n); split; [left; reflexivity | cbn; lia] | apply Forall_nil]. }
    assert (DSH2 : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(p, p + 8 * n)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO; clear - HpA'; lia | apply Forall_nil]. }
    assert (ADP2 : addressable M2 p (8 * n)) by (eapply addressable_transport; [exact ADP1 | exact MU2 | exact WM2 | apply DSH2; lia]).
    assert (ADH2 : addressable M2 obj 40) by (eapply addressable_transport; [exact ADH1 | exact MU2 | exact WM2 | apply DSH2; lia]).
    assert (ADN2 : forall e, In e ents -> addressable M2 (addr e) 32).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _). eapply addressable_transport; [exact (ADN1 e He) | exact MU2 | exact WM2 | apply DSH2; lia]. }
    assert (ADPN2 : addressable M2 pn 32) by (eapply addressable_transport; [exact ADPN1 | exact MU2 | exact WM2 | apply DSH2; lia]).
    assert (HNI : ~ In pid (map blk_id ((qn, pn, 32) :: LBn))).
    { assert (ND1 : List.NoDup (map blk_id (LB0 ++ (pid, p, 8 * n) :: (qn, pn, 32) :: LBn)))
        by (eapply Permutation_NoDup; [apply Permutation_map; exact PE | exact (ah_nodup H HH _ _ _ RH)]).
      rewrite map_app in ND1. apply NoDup_app_remove_l in ND1. cbn [map] in ND1.
      inversion ND1 as [|z l Hni Hnd]; subst. exact Hni. }
    assert (HPQ : apart p (8 * n) pn 32).
    { assert (Hne : pid <> qn) by (intros E; apply HNI; left; cbn; exact (eq_sym E)).
      pose proof (ah_disj H HH _ _ _ _ _ RH INP INQ Hne) as D. cbn [blk_addr blk_size blk_id Datatypes.fst Datatypes.snd] in D.
      unfold apart. clear - D. lia. }
    assert (TS2 : forall A cs, rw_cells asegs M1 A cs -> p + 8 * n <= A \/ A + Z.of_nat (cells_size cs) <= p -> rw_cells asegs M2 A cs).
    { intros A cs C D. eapply rw_cells_transport; [exact C | exact MU2 | exact WM2 | cbn [disjoint_from]; lia]. }
    pose proof WS1 as (WT584 & WT600 & WT632 & WT656). pose proof NS1 as (NT408 & NT576 & NT616 & NT624 & NT648).
    assert (WS2 : WSLOTS ty enc S1 obj M2 j584 (Z_to_bv 64 (pn / 8 + SHBASE))).
    { split; [apply TS2; [exact WT584 | cbn; lia]|]. split; [apply TS2; [exact WT600 | cbn; lia]|].
      split; [apply TS2; [exact WT632 | cbn; lia] | apply TS2; [exact WT656 | cbn; lia]]. }
    assert (NS2 : nt_slots M2 S1 obj v408 v576 v624).
    { split; [apply TS2; [exact NT408 | cbn; lia]|]. split; [apply TS2; [exact NT576 | cbn; lia]|].
      split; [apply TS2; [exact NT616 | cbn; lia]|]. split; [apply TS2; [exact NT624 | cbn; lia] | apply TS2; [exact NT648 | cbn; lia]]. }
    assert (ERR2 : rw_cells asegs M2 (errno_addr tp) [C4 errv]) by (apply TS2; [exact ERR1 | rewrite EA; cbn; clear - HpI; unfold ATP in *; lia]).
    assert (CPN2 : rw_cells asegs M2 pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)])
      by (apply TS2; [exact CPN1 | cbn; clear - HPQ; unfold apart in HPQ; lia]).
    assert (OUT2 : forall a k, 0 <= a -> a + k <= aceil -> apart a k p (8 * n) -> agree_on M1 M2 a k).
    { intros a k Ha Hak Hap. eapply agree_of_munch; [exact MU2 | | lia | clear - Hak ACF2; lia]. intros z Hz. cbn. unfold apart in Hap. clear - Hz Hap Hak. lia. }
    assert (NODES2 : forall e, In e ents -> agree_on m0 M2 (addr e) 32).
    { intros e He. destruct (ent_facts _ _ _ _ _ _ e U0 He) as (He0 & He1 & _).
      destruct (lbl_in_inv LBn (addr e) 32 (Permutation_in _ (Permutation_sym PM) (in_map (fun e0 : ent => (addr e0, 32)) _ _ He))) as (q & Hq).
      assert (HqL : In (q, addr e, 32) LB') by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; right; right; exact Hq).
      pose proof (ah_blocks H HH _ _ _ _ RH HqL) as (_ & _ & _ & _ & QC & _). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in QC.
      assert (Hne : pid <> q) by (intros E; apply HNI; right; apply (in_map blk_id) in Hq; cbn in Hq |- *; rewrite E; exact Hq).
      pose proof (ah_disj H HH _ _ _ _ _ RH INP HqL Hne) as D. cbn [blk_addr blk_size blk_id Datatypes.fst Datatypes.snd] in D.
      eapply agree_on_trans; [exact (NODES1 e He) | apply OUT2; [lia | exact QC | unfold apart; clear - D; lia]]. }
    assert (HDR2 : agree_on m0 M2 (obj + 16) 24).
    { eapply agree_on_trans; [exact HDR1 | apply OUT2; [lia | lia | clear - HPO; unfold apart in *; lia]]. }
    assert (Cbl2 : cell8 ASEGS M2 obj p) by (eapply cellw_agree; [exact Cbl1 | apply OUT2; [lia | lia | clear - HPO; unfold apart in *; lia] | lia | cbn; lia]).
    assert (Cbc2 : cell8 ASEGS M2 (obj + 8) n).
    { apply (cellw8_of_rw_cells M2 (obj + 8) n); [| lia | lia].
      apply TS2; [exact Cbc1 | cbn; clear - HPO; unfold apart in HPO; lia]. }
    assert (OWN2 : lb_own ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) M2) by exact (lb_own_wmono _ _ _ OWN1 WM2).
    assert (WRH2 : wr_at asegs M2 obj 40) by exact (wr_at_wmono _ _ _ _ WRH1 WM2).
    eapply (stage_post H HHB gp tp s0 s4 ty wd enc S1 sk0 LB0 LF obj key v408 v576 v624 ents bl bc lo B shi m0 mo0 LBe
              U0 Hlast OCE LFO ACL LOS TPV KR32 ZLEN s msF1 mo1 M2 F fc).
    1: exact VIS1.
    all: first [ eassumption | exact (ah_mpres_trans H HH _ _ _ MP MP1) ].
  Qed.

  Lemma stage_b_z : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word) (errv : word) (LB LBm : list block) (pid qn : bptr) (p pn : Z)
      (junk : list byte) (j584 : word),
    as_VIS H s msF = MS (mkR (Z_to_bv 64 R_NEWRET) (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 key) y19 s4 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 pn) wd
                             (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29 y30 y31)
                        F (Z_to_bv 64 R_NEWRET) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS ty enc S1 obj m j584 (Z_to_bv 64 (pn / 8 + SHBASE)) -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> (0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64) ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 32) -> agree_on m0 m obj 40 ->
    (bc <> 0 -> addressable m bl (8 * bc)) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 32) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s ((pid, p, 8 * n) :: LB) m ->
    Permutation LB (LB0 ++ (qn, pn, 32) :: LBm) -> Permutation (lbl LBm) (umap_blocks 32 bl bc ents) -> lb_own ((qn, pn, 32) :: LBm) m ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) junk] -> addressable m p (8 * n) ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    rw_cells asegs m pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    addressable m pn 32 -> (bc = 0 \/ Zlength ents = bc) ->
    as_chain H m (bv_unsigned s0) CH ->
    bc = 0 ->
    as_SR H QIx (mkCfg msF mo).
  Proof using HHB U0 Hlast OCE LFO ACL LOS TPV KR32 ZLEN.
    intros s msF mo m F fc y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 errv LB LBm pid qn p pn junk j584
      VIS FRZ KR MP WS NS SPL SPH V64 MI ST ERR RA NODES HDR ADB ADH ADN WRH RH PE PM OWN PBLK ADP XP RF AC S0 AL NC ADPN GROW CHN BZ.
    pose proof (aceil_facts) as ((ACF1 & ACF2) & _ & _).
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U0)) as BCR.
    destruct (LbB_HEmpR.bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & _).
    assert (Hn0 : 0 < n) by (clear - BCR Hbcn; lia).
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (VA & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof VA as HoA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in HoA.
    pose proof (ah_blocks H HH _ _ _ _ RH (or_introl eq_refl)) as (Hp0 & Hp16 & _ & HpI & HpC & HpF & HpA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hp0, Hp16, HpI, HpC, HpF, HpA. unfold AIMG_TOP in HpI.
    assert (HPO : apart p (8 * n) obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HpF OB1 OB2 Hn0; lia).
    assert (QNL : In (qn, pn, 32) ((pid, p, 8 * n) :: LB)).
    { right. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. left. reflexivity. }
    pose proof (ah_blocks H HH _ _ _ _ RH QNL) as (Hq0 & Hq16 & _ & HqI & HqC & HqF & HqA).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hq0, Hq16, HqI, HqC, HqF, HqA. unfold AIMG_TOP in HqI.
    assert (HQO : apart pn 32 obj 40) by (unfold apart; unfold AFS_SIZE in *; clear - HqF OB1 OB2; lia).
    assert (GZO : gz m obj 40) by (apply LbB_HEmpI.gzA; [exact ADH | reflexivity]).
    pose proof (gz_at m obj 40 0 GZO ltac:(lia)) as SH0. rewrite Z.add_0_r in SH0.
    destruct (u_hdr U0) as [Cbl0 _ _ _ _ _].
    assert (Cbl : cell8 ASEGS m obj bl) by (eapply cellw_agree; [exact Cbl0 | eapply agree_on_sub; [exact HDR | lia | cbn; lia] | lia | cbn; lia]).
    destruct (u_blive U0) as [[_ Hbl] | [Hbc _]]; [| exfalso; lia].
    assert (HE : ents = []) by (eapply ents_nil_of_bc0; [exact U0 | exact BZ]).
    pose proof WS as WS0. destruct WS0 as (W584 & W600 & W632 & W656).
    pose proof NS as NS0. destruct NS0 as (N408 & N576 & N616 & N624 & N648).
    remember (mkR (Z_to_bv 64 R_NEWRET) (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 key) y19 s4 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 pn) wd
                  (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29 y30 y31) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 p; Z_to_bv 64 (obj / 8); Z_to_bv 64 (obj + 8); Z_to_bv 64 SHBASE]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (10%bv, EVar 34); (25%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (HK : know_ok asegs E m (kn_fix 20 [R_JN] (SCR [] [ELit 0] []) R_NEWRET
                   (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (10%bv, EVar 34); (25%bv, EVar 33)])
                   [KWord (SA (EVar 32) 616) 8 (EVar 37); KWord (SA (EVar 32) 640) 8 (EVar 35); KWord (SA (EVar 32) 632) 8 (EVar 36);
                    KWord (SA (EAlu ALU_ADD (EVar 35) (EVar 37)) 0) 1 (ELit 0); KWord (SA (EAlu ALU_ADD (EVar 37) (EVar 35)) 0) 1 (ELit 0);
                    KWr (SA (EVar 33) 0) (ELit 8); KRange (EVar 33) 7241728 (2 ^ 47 - 40); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)] 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell N616 0%nat (C8 (Z_to_bv 64 SHBASE))|].
      apply Forall_cons; [kword_cell W632 8%nat (C8 (Z_to_bv 64 (obj / 8)))|].
      apply Forall_cons; [kword_cell W632 0%nat (C8 (Z_to_bv 64 (obj + 8)))|].
      do 2 (apply Forall_cons; [eapply (kshadow0_reg E m _ obj);
        [evs; rewrite w_add by (clear - Ho0 Ho1; unfold SHBASE; Z.div_mod_to_equations; lia); first [reflexivity | f_equal; lia] | lia | exact SH0]|]).
      apply Forall_cons; [eapply (kwr_of_wr_at asegs E m obj 40); [exact WRH | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - OB3 Ho1; lia|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; clear - SPL SPH; lia|].
      clear - GZO Ho0 Ho1 OB3. know_tac. }
    assert (Hrd_bl : sc_denot asegs m E (SCReadBase (SA (EVar 33) 0) 8 false (ELit 0))).
    { rewrite Hbl in Cbl. eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbl); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    xrun_at (PropExec.mkFP F fc) asegs R R_NEWRET m (seg_rom asegs) HR HK 40%nat [R_JN] (SCR [] [ELit 0] []) 50%N.
    { split_scs; [exact Hrd_bl |].
      clear - E Ho0 Ho1. cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [edenot a_base a_off].
      rewrite w_add by (unfold SHBASE; Z.div_mod_to_equations; lia).
      rewrite ?u64_of_Z by (unfold SHBASE; Z.div_mod_to_equations; lia). unfold SHBASE; Z.div_mod_to_equations; lia. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(obj, obj + 8)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
    assert (Cbl1 : cell8 ASEGS M1 obj p).
    { apply (cellw8_of_rw_cells M1 obj p); [| lia | lia]. subst M1. rwc_new Hlf (LbB_HEmpD.wr_at_subE m obj 40 obj 8 WRH ltac:(lia) ltac:(lia) ltac:(lia)). }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 13%bv G13. rreg HR' 21%bv G21. rreg HR' 22%bv G22. rreg HR' 25%bv G25.
    rreg HR' 30%bv G30. rreg HR' 31%bv G31.
    assert (G21' : getr R' 21 = Z_to_bv 64 (obj / 8 + SHBASE)).
    { rewrite G21. rewrite w_add by (clear - Ho0 Ho1; unfold SHBASE; Z.div_mod_to_equations; lia). first [reflexivity | f_equal; lia]. }
    assert (G30' : getr R' 30 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G30, HR0; reflexivity).
    assert (G31' : getr R' 31 = Z_to_bv 64 (2 ^ 60)) by (rewrite G31, HR0; reflexivity).
    rewrite G2, G9, G13, G21', G22, G25, G30', G31' in HRe. clear G21 G30 G31.
    destruct (LbB_HEmpD.obj_window_ok H HH LF obj ((pid, p, 8 * n) :: LB) m obj (obj + 8) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
    destruct (client_frame H HH s ((pid, p, 8 * n) :: LB) LF B [(obj, obj + 8)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_nil _)) (Forall_cons _ _ _ W2 (Forall_nil _)) (Forall_cons _ _ _ W3 (Forall_nil _)))
      as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_nil _))]).
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { rewrite TPV in ERR |- *. unfold errno_addr in ERR |- *. rewrite u64_of_Z in ERR |- * by (unfold ATP; lia).
      eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 | cbn; unfold ATP; lia]. }
    assert (HIN : forall a k, 0 <= a -> a + k <= 2 ^ 64 -> (a + k <= obj \/ obj + 8 <= a) -> agree_on m M1 a k).
    { intros a k Ha Hak Hd. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz Hd. lia. }
    assert (DSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(obj, obj + 8)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      apply Forall_cons; [cbn [Datatypes.fst Datatypes.snd]; unfold ALOWSH_LO, AHI_LO; clear - HoA; lia | apply Forall_nil]. }
    assert (WS1 : WSLOTS ty enc S1 obj M1 j584 (Z_to_bv 64 (pn / 8 + SHBASE))).
    { unfold WSLOTS, nt_wslots. split; [|split; [|split]];
        (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | cbn; lia]). }
    assert (NS1 : nt_slots M1 S1 obj v408 v576 v624).
    { unfold nt_slots. repeat match goal with |- _ /\ _ => split end;
        (eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | cbn; lia]). }
    assert (PBLK1 : rw_cells asegs M1 p [CB (Z.to_nat (8 * n)) junk]).
    { eapply rw_cells_transport; [exact PBLK | exact MU1 | exact WM1 |].
      cbn [disjoint_from cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; clear - HPO; unfold apart in HPO; lia. }
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m0 M1).
    { eapply (xpres_trans H); [exact XP|].
      eapply (xpres_weaken H); [eapply (xpres_of_munch H s ((pid, p, 8 * n) :: LB) S1 (nt_X S1 obj) [(obj, obj + 8)] m m M1 HH RH MU1 WM1) | lia | |].
      - apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; left; lia | apply Forall_nil].
      - intros b Hb. right. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb.
      - intros a Ha. exact Ha. }
    assert (PMn : Permutation (lbl LBm) (map (fun e : ent => (addr e, 32)) ents)).
    { unfold umap_blocks in PM. rewrite BZ in PM. cbn [Z.eqb app] in PM. exact PM. }
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    eapply (stage_c s msF1 mo1 M1 F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ errv ((pid, p, 8 * n) :: LB) LBm pid qn p pn junk j584);
      [ exact VIS1 | exact FRZ | exact KR1 | eapply (ah_mpres_trans H HH); [exact MP | exact MP1]
      | exact WS1 | exact NS1 | exact SPL | exact SPH | exact V64 | exact MI1 | exact ST1 | exact ERR1 | exact RA1
      | intros e He; rewrite HE in He; destruct He
      | eapply agree_on_trans; [eapply agree_on_sub; [exact HDR | lia | lia] | apply HIN; lia]
      | exact Cbl1 | exact PBLK1
      | eapply addressable_transport; [exact ADP | exact MU1 | exact WM1 | apply DSH; lia]
      | eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH; lia]
      | intros e He; rewrite HE in He; destruct He
      | exact (wr_at_wmono _ _ _ _ WRH WM1)
      | exact RH1
      | eapply perm_trans; [apply perm_skip; exact PE | apply Permutation_middle]
      | exact PMn
      | apply lb_own_cons; [cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; exact (own_of_rw_cells _ _ _ _ PBLK1 ltac:(lia)) | exact (lb_own_wmono _ _ _ OWN WM1)]
      | exact XP1 | exact RF1 | exact AC1 | exact S01 | exact AL
      | eapply rw_cells_transport; [exact NC | exact MU1 | exact WM1 | cbn [disjoint_from cells_size csize Z.of_nat]; clear - HQO; unfold apart in HQO; lia]
      | eapply addressable_transport; [exact ADPN | exact MU1 | exact WM1 | apply DSH; lia]
      | exact GROW ].
  Qed.

  Lemma stage_b_nz : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word) (errv : word) (LB LBm : list block) (pid qn : bptr) (p pn : Z)
      (junk : list byte) (j584 : word),
    bc <> 0 ->
    as_VIS H s msF = MS (mkR (Z_to_bv 64 R_NEWRET) (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 key) y19 s4 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 pn) wd
                             (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29 y30 y31)
                        F (Z_to_bv 64 R_NEWRET) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS ty enc S1 obj m j584 (Z_to_bv 64 (pn / 8 + SHBASE)) -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> (0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64) ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 32) -> agree_on m0 m obj 40 ->
    (bc <> 0 -> addressable m bl (8 * bc)) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 32) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s ((pid, p, 8 * n) :: LB) m ->
    Permutation LB (LB0 ++ (qn, pn, 32) :: LBm) -> Permutation (lbl LBm) (umap_blocks 32 bl bc ents) -> lb_own ((qn, pn, 32) :: LBm) m ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) junk] -> addressable m p (8 * n) ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    rw_cells asegs m pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    addressable m pn 32 -> (bc = 0 \/ Zlength ents = bc) ->
    as_chain H m (bv_unsigned s0) CH ->
    as_SR H QIx (mkCfg msF mo).
  Proof using HHB U0 Hlast AL0 OCE LFO ACL LOS LOR TPV KR32 ZLEN SP16 SPB TRK CHH.
    intros s msF mo m F fc y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 errv LB LBm pid qn p pn junk j584
      Hbc VIS FRZ KR MP WS NS SPL SPH V64 MI ST ERR RA NODES HDR ADB ADH ADN WRH RH PE PM OWN PBLK ADP XP RF AC S0 AL NC ADPN GROW CHN.
    assert (AGA : forall LBx SP m1 m1' a k, apres H LBx SP m1 m1' -> aclient_range H LBx SP a k -> 0 <= a -> a + k <= 2 ^ 64 -> agree_on m1 m1' a k).
    { intros LBx SP m1 m1' a k AP CR Ha Hak i Hi.
      destruct (AP (a + i) ltac:(lia) (aclient_range_addr H _ _ _ _ (a + i) CR ltac:(lia))) as [Eq _]. exact Eq. }
    assert (LPS : forall (LBs : list block) (l1 l2 : list (Z * Z)),
      Permutation (lbl LBs) (l1 ++ l2) -> exists L1 L2, Permutation LBs (L1 ++ L2) /\ lbl L1 = l1 /\ lbl L2 = l2).
    { intros LBs l1 l2 P. apply Permutation_sym in P. unfold lbl in P.
      apply Permutation_map_inv in P. destruct P as (l3 & Eq & P3).
      symmetry in Eq. apply map_eq_app in Eq. destruct Eq as (L1 & L2 & E3 & E1 & E2). subst l3.
      exists L1, L2. split; [exact P3|]. split; [exact E1 | exact E2]. }
    destruct (LbB_HEmpR.bseq_next_factsE bc (u_bseq U0) Hlast) as (HnB & Hbcn & Hn28 & _).
    pose proof (LbB_HFind.BSEQ_boundA bc (u_bseq U0)) as Hbc0.
    assert (Hn0 : 0 < n) by lia.
    pose proof LOR as LOR'. unfold ANT_STACK, AOPNEW_STACK, AMALLOC_STACK in LOR'.
    pose proof (u_obj_lo U0) as Ho0. pose proof (u_obj_hi U0) as Ho1. pose proof (u_obj_al U0) as Hoal.
    pose proof (LbB_HEmpD.obj_place H HH LF obj m RF LFO) as (OAPP & OB1 & OB2 & OB3). unfold AIMG_TOP in OB3.
    pose proof OAPP as HoA. unfold aapp, aapp_lo, aapp_hi, ALOWSH_LO, AHI_LO, AIMG_TOP in HoA.
    pose proof (ah_fsb H HH _ _ _ RH) as (FB1 & FB2 & FB3 & FB4).
    pose proof (u_bl_lo U0 Hbc) as Hbl0. pose proof (u_bl_hi U0) as Hbl1.
    assert (BLK : forall b, In b ((pid, p, 8 * n) :: LB) ->
              0 < blk_addr b /\ 0 <= blk_size b /\ AIMG_TOP <= blk_addr b /\ blk_addr b + blk_size b <= aceil
              /\ (blk_addr b + blk_size b <= obj \/ obj + 40 <= blk_addr b)).
    { intros b Hb. pose proof (ah_blocks H HH _ _ _ _ RH Hb) as (B0 & B16 & Bn & BI & BC & BF & BA).
      clear - B0 Bn BI BC BF OB1 OB2. lia. }
    assert (INN : In (qn, pn, 32) ((pid, p, 8 * n) :: LB)).
    { right. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. left. reflexivity. }
    pose proof (BLK _ (or_introl eq_refl)) as (Hp0 & _ & HpI & HpC & HpO). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hp0, HpI, HpC, HpO.
    pose proof (BLK _ INN) as (Hq0 & _ & HqI & HqC & HqO). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hq0, HqI, HqC, HqO.
    assert (GZh : gz m obj 40) by (apply LbB_HEmpI.gzA; [exact ADH | reflexivity]).
    destruct (u_hdr U0) as [Cbl0 Cbc0 _ _ _ _].
    assert (Cbl : cell8 ASEGS m obj bl) by (eapply cellw_agree; [exact Cbl0 | eapply agree_on_sub; [exact HDR | lia | cbn; lia] | lia | cbn; lia]).
    assert (Cbc : cell8 ASEGS m (obj + 8) bc) by (eapply cellw_agree; [exact Cbc0 | eapply agree_on_sub; [exact HDR | lia | cbn; lia] | lia | cbn; lia]).
    unfold umap_blocks in PM. destruct (Z.eqb_spec bc 0) as [|_]; [lia|].
    destruct (LPS LBm _ _ PM) as (LBk & LBn & PS & EK & EN).
    assert (EKq : exists qb, LBk = [(qb, bl, 8 * bc)]).
    { destruct LBk as [|[[q A] N] [|b LBk']]; cbn in EK; try discriminate EK. injection EK as -> ->. exists q. reflexivity. }
    destruct EKq as (qb & ->). cbn [app] in PS.
    assert (PMn : Permutation (lbl LBn) (map (fun e : ent => (addr e, 32)) ents)) by (rewrite EN; apply Permutation_refl).
    assert (INQm : In (qb, bl, 8 * bc) LBm) by (apply (Permutation_in _ (Permutation_sym PS)); left; reflexivity).
    assert (INQL : In (qb, bl, 8 * bc) LB) by (apply (Permutation_in _ (Permutation_sym PE)); apply in_or_app; right; right; exact INQm).
    assert (INQ : In (qb, bl, 8 * bc) ((pid, p, 8 * n) :: LB)) by (right; exact INQL).
    pose proof (BLK _ INQ) as (Hb0 & _ & HbI & HbC & HbO). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in Hb0, HbI, HbC, HbO.
    assert (NDL : List.NoDup (map blk_id ((pid, p, 8 * n) :: LB))) by exact (ah_nodup H HH _ _ _ RH).
    assert (Hqp : pid <> qb).
    { intros Eq. pose proof NDL as ND'. cbn [map] in ND'. apply NoDup_cons_iff in ND'. destruct ND' as [NI _]. apply NI.
      rewrite Eq. apply (in_map blk_id) in INQL. exact INQL. }
    assert (PE1 : Permutation ((pid, p, 8 * n) :: LB) ((LB0 ++ [(pid, p, 8 * n); (qn, pn, 32)]) ++ (qb, bl, 8 * bc) :: LBn)).
    { rewrite <- app_assoc. cbn [app].
      eapply perm_trans; [apply perm_skip; eapply perm_trans; [exact PE | apply Permutation_app_head; apply perm_skip; exact PS] |].
      apply Permutation_middle. }
    assert (ENT : forall e, In e ents -> exists q, In (q, addr e, 32) LBn /\ 0 < addr e /\ AIMG_TOP <= addr e /\ addr e + 32 <= aceil
                    /\ (addr e + 32 <= obj \/ obj + 40 <= addr e)).
    { intros e He. destruct (lbl_in_inv LBn (addr e) 32 (Permutation_in _ (Permutation_sym PMn) (in_map (fun e0 : ent => (addr e0, 32)) _ _ He))) as (q & Hq).
      exists q. split; [exact Hq|].
      assert (INe : In (q, addr e, 32) ((pid, p, 8 * n) :: LB)).
      { right. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. right. right. apply (Permutation_in _ (Permutation_sym PS)). right. exact Hq. }
      pose proof (BLK _ INe) as (E0 & _ & EI & EC & EO). cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in E0, EI, EC, EO. lia. }
    destruct WS as (W584 & W600 & W632 & W656).
    pose proof NS as (N408 & N576 & N616 & N624 & N648).
    remember (mkR (Z_to_bv 64 R_NEWRET) (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                  (Z_to_bv 64 key) y19 s4 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 pn) wd
                  (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29 y30 y31) as R eqn:HR0.
    assert (FHF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose (E := Eseed R [Z_to_bv 64 S1; Z_to_bv 64 obj; Z_to_bv 64 p; Z_to_bv 64 bl; Z_to_bv 64 bc; Z_to_bv 64 (sh (obj + 8))]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (25%bv, EVar 33); (10%bv, EVar 34)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R; evs; reflexivity] |]). apply Forall_nil. }
    assert (Hrd_bl : sc_denot asegs m E (SCReadBase (SA (EVar 33) 0) 8 false (EVar 35))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbl); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (Hrd_bc : sc_denot asegs m E (SCReadBase (SA (EVar 33) 8) 8 false (EVar 36))).
    { eapply (sc_read_cellw _ _ _ _ _ _ _ _ Cbc); [cbn; lia | evs; rewrite v_addi_Z by lia; f_equal; lia | evs; reflexivity]. }
    assert (HK : know_ok asegs E m (kn_fix 20 [AOPDEL2; R_DRET] (SCR [] [EVar 35; EVar 36] []) R_NEWRET
        (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32); (25%bv, EVar 33); (10%bv, EVar 34)])
        [KWord (SA (EVar 32) 616) 8 (ELit SHBASE); KWord (SA (EVar 32) 640) 8 (EAlu ALU_SRL (EVar 33) (ELit 3));
         KWord (SA (EVar 32) 632) 8 (EAlu ALU_ADD (EVar 33) (ELit 8)); KWord (SA (EVar 32) 664) 8 (EVar 37);
         KWord (SA (EVar 37) 0) 1 (ELit 0); KWr (SA (EVar 33) 0) (ELit 8); KWr (SA (EVar 32) 584) (ELit 8);
         KRange (EVar 35) 1 (2 ^ 47); KRange (EVar 33) 7241728 (2 ^ 47 - 40); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)] 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell N616 0%nat (C8 (Z_to_bv 64 SHBASE))|].
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 8%nat (C8 (Z_to_bv 64 (obj / 8))));
          [ exact W632 | reflexivity | reflexivity | lia
          | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        assert (EV : edenot E (EAlu ALU_SRL (EVar 33) (ELit 3)) = Z_to_bv 64 (obj / 8)) by (evs; rewrite HWord.w_srl by lia; reflexivity).
        rewrite EV. reflexivity. }
      apply Forall_cons.
      { eapply (kword_of_rw_cells _ _ _ _ _ 0%nat (C8 (Z_to_bv 64 (obj + 8))));
          [ exact W632 | reflexivity | reflexivity | lia
          | unfold SymExec3Sound.SX2S.estart; HLib.evs; rewrite ?HLib.u64_of_Z by lia; cbn [SymExec3.SX2.a_off Z.of_nat Pos.of_succ_nat Pos.succ]; lia
          | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia |].
        assert (EV : edenot E (EAlu ALU_ADD (EVar 33) (ELit 8)) = Z_to_bv 64 (obj + 8)) by (evs; rewrite w_add by lia; reflexivity).
        rewrite EV. reflexivity. }
      apply Forall_cons; [kword_cell W656 8%nat (C8 (Z_to_bv 64 (sh (obj + 8))))|].
      apply Forall_cons; [eapply (kshadow0_reg E m (EVar 37) (obj + 8)); [evs; unfold sh; rewrite ASHADOW_BASE_val; unfold SHBASE; f_equal; lia | lia | exact (gz_at m obj 40 8 GZh ltac:(lia))]|].
      apply Forall_cons; [eapply (kwr_of_wr_at asegs E m obj 40); [exact WRH | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]|].
      apply Forall_cons; [eapply (kwr_of_stk asegs E m lo (S1 + 672)); [exact ST | rwc_norm | unfold elenZ; rwc_norm | unfold elenZ; evs; rewrite u64_of_Z by lia; lia]|].
      do 3 (apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|]).
      clear - GZh Ho0 Ho1 OB3. know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R R_NEWRET m (seg_rom asegs) HR HK 40%nat [AOPDEL2; R_DRET] (SCR [] [EVar 35; EVar 36] []) 50%N.
    { split_scs; first [ exact Hrd_bl | exact Hrd_bc | sc_dj
                       | cbn [sc_denot]; unfold flat, estart, elenZ; evs; cbn [edenot a_base a_off]; unfold sh; rewrite ?ASHADOW_BASE_val; unfold SHBASE;
                         rewrite ?u64_of_Z by (Z.div_mod_to_equations; lia); Z.div_mod_to_equations; lia ]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    assert (MU1 : munch [(obj, obj + 8); (S1 + 584, S1 + 592)] m M1).
    { subst M1. apply munch_mem_denot; [exact Hlf|].
      repeat (apply Forall_cons; [cbn [e_addr e_width]; unfold estart; evs; rewrite ?u64_of_Z by lia; cbn [inside a_off a_base Z.of_nat Pos.of_succ_nat Pos.succ]; lia|]).
      apply Forall_nil. }
    assert (WM1 : wmono asegs m M1) by (subst M1; apply wmono_mem_denot).
    assert (MI1 : mem_inv asegs M1) by exact (msteps_mem_inv asegs _ _ Hms MI).
    assert (ST1 : stk asegs M1 lo (S1 + 672)) by (subst M1; apply stk_mem_denot; exact ST).
    assert (Cbl1 : cell8 ASEGS M1 obj p).
    { apply (cellw8_of_rw_cells M1 obj p); [| lia | lia]. subst M1. rwc_new Hlf (LbB_HEmpD.wr_at_subE m obj 40 obj 8 WRH ltac:(lia) ltac:(lia) ltac:(lia)). }
    assert (W5841 : rw_cells asegs M1 (S1 + 584) [C8 (Z_to_bv 64 0)]).
    { subst M1. rwc_new Hlf (LbB_HEmpD.wr_at_subE m lo (S1 + 672 - lo) (S1 + 584) 8 (wr_at_of_stk asegs m lo (S1 + 672) ST) ltac:(lia) ltac:(lia) ltac:(lia)). }
    destruct (LbB_HEmpD.obj_window_ok H HH LF obj ((pid, p, 8 * n) :: LB) m obj (obj + 8) RF LFO ltac:(lia) ltac:(lia)) as (W1 & W2 & W3 & W4).
    assert (ACS : aceil <= S1 + 584) by lia.
    destruct (stack_window_ok H ((pid, p, 8 * n) :: LB) LF (S1 + 584) (S1 + 592) ACS FB2) as (W5 & W6 & W7).
    assert (W8 : stack0_ok (S1 + 584, S1 + 592)) by (left; cbn; unfold AHI_LO; lia).
    destruct (client_frame H HH s ((pid, p, 8 * n) :: LB) LF B [(obj, obj + 8); (S1 + 584, S1 + 592)] m M1 RH RF AC RA MU1 WM1
               (Forall_cons _ _ _ W1 (Forall_cons _ _ _ W5 (Forall_nil _))) (Forall_cons _ _ _ W2 (Forall_cons _ _ _ W6 (Forall_nil _)))
               (Forall_cons _ _ _ W3 (Forall_cons _ _ _ W7 (Forall_nil _)))) as (RH1 & RF1 & AC1 & RA1).
    assert (S01 : stack0 M1 lo shi) by (eapply stack0_transport; [exact S0 | exact MU1 | exact WM1 | exact (Forall_cons _ _ _ W4 (Forall_cons _ _ _ W8 (Forall_nil _)))]).
    assert (DSH : forall A k, 0 <= A -> 0 <= k -> A + k <= 2 ^ 47 -> disjoint_from [(obj, obj + 8); (S1 + 584, S1 + 592)] (sh A) (nsh k)).
    { intros A k HA Hk HAk. apply LbB_HEmpI.dsh_app; [| exact HA | exact Hk | exact HAk].
      apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO; clear - HoA; lia|].
      apply Forall_cons; [cbn [fst snd]; unfold ALOWSH_LO, AHI_LO; clear - SPL; lia | apply Forall_nil]. }
    assert (HIN : forall a k, 0 <= a -> a + k <= 2 ^ 64 -> (a + k <= obj \/ obj + 8 <= a) -> (a + k <= S1 + 584 \/ S1 + 592 <= a) -> agree_on m M1 a k).
    { intros a k Ha Hak Hd1 Hd2. eapply agree_of_munch; [exact MU1 | | lia | lia]. intros z Hz. cbn. clear - Hz Hd1 Hd2. lia. }
    assert (EAB : 0 <= errno_addr tp /\ errno_addr tp + 4 <= AIMG_TOP).
    { rewrite TPV. unfold AIMG_TOP. vm_compute. split; intro X; discriminate X. }
    assert (ERR1 : rw_cells asegs M1 (errno_addr tp) [C4 errv]).
    { eapply rw_cells_transport; [exact ERR | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize Z.of_nat Nat.add]. unfold AIMG_TOP in EAB. lia. }
    assert (W584M : rw_cells asegs M1 (S1 + 584) [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (pn / 8 + SHBASE))]).
    { pose proof W584 as W584c.
      change [C8 j584; C8 (Z_to_bv 64 (pn / 8 + SHBASE))] with ([C8 j584] ++ [C8 (Z_to_bv 64 (pn / 8 + SHBASE))]) in W584c.
      apply rw_cells_app in W584c. destruct W584c as [_ W592].
      replace (S1 + 584 + Z.of_nat (cells_size [C8 j584])) with (S1 + 592) in W592 by (cbn; lia).
      change [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 (pn / 8 + SHBASE))] with ([C8 (Z_to_bv 64 0)] ++ [C8 (Z_to_bv 64 (pn / 8 + SHBASE))]).
      apply rw_cells_app. split; [exact W5841|].
      replace (S1 + 584 + Z.of_nat (cells_size [C8 (Z_to_bv 64 0)])) with (S1 + 592) by (cbn; lia).
      eapply rw_cells_transport; [exact W592 | exact MU1 | exact WM1 | cbn; lia]. }
    assert (OWNm : lb_own LBm m) by (eapply lb_own_incl; [| exact OWN]; intros b Hb; right; exact Hb).
    destruct (rw_cells_of_own LBm M1 (qb, bl, 8 * bc) (lb_own_wmono _ _ _ OWNm WM1) INQm ltac:(cbn [blk_addr Datatypes.fst Datatypes.snd]; lia)
                ltac:(cbn [blk_size Datatypes.snd]; lia)) as (obs & OBS).
    cbn [blk_addr blk_size Datatypes.fst Datatypes.snd] in OBS.
    assert (ADB1 : addressable M1 bl (8 * bc)) by (eapply addressable_transport; [exact (ADB Hbc) | exact MU1 | exact WM1 | apply DSH; lia]).
    assert (CHN1 : as_chain H M1 (bv_unsigned s0) CH).
    { eapply (chain_keep H HH m M1 _ CH S1); [exact CHN | exact CHH |]. intros a Ha. apply MU1. rewrite wa_unsigned by lia. cbn [outside]. lia. }
    readback HR' (msteps_full asegs _ _ Hms FHF) HR0 HRe.
    rreg HR' 1%bv G1. rreg HR' 2%bv G2. rreg HR' 9%bv G9. rreg HR' 10%bv G10. rreg HR' 11%bv G11. rreg HR' 13%bv G13.
    rreg HR' 19%bv G19. rreg HR' 21%bv G21. rreg HR' 22%bv G22. rreg HR' 25%bv G25. rreg HR' 30%bv G30. rreg HR' 31%bv G31.
    assert (G1' : getr R' 1 = Z_to_bv 64 R_DRET) by (rewrite G1; reflexivity).
    assert (G19' : getr R' 19 = Z_to_bv 64 (2 ^ 60)) by (rewrite G19, HR0; reflexivity).
    assert (G25' : getr R' 25 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G25, HR0; reflexivity).
    assert (G30' : getr R' 30 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite G30, HR0; reflexivity).
    assert (G31' : getr R' 31 = Z_to_bv 64 (2 ^ 60)) by (rewrite G31, HR0; reflexivity).
    rewrite (w_mul 8 bc) in G11 by lia. rewrite (LbB_NtD.sh_word obj) in G21 by lia. rewrite (w_add obj 8) in G22 by lia.
    rewrite G1', G2, G9, G10, G11, G13, G19', G21, G22, G25', G30', G31' in HRe.
    eapply (sr_blk_eq H HH); [exact KR | exact VIS | exact FHF | exact Hms | exact HRe |].
    intros msF1 mo1 KR1 MP1 VIS1.
    clear HRe Hlf. rename R' into R1. rename HR' into HR1. rename Hms into Hms1.
    eapply (ah_seq H HH).
    { eapply (ah_opdel2 H HH) with (p := qb) (A := bl) (n := 8 * bc) (LB := (pid, p, 8 * n) :: LB) (lo := lo) (B := B) (errv := errv) (CH := CH)
          (bs := obs) (sbs := shadow_of (8 * bc));
        [ exact VIS1 | exact RH1 | exact KR1 | exact INQ | rewrite (proj1 (rt_bp_cost H HHB)); clear - AL AL0; lia
        | exact OBS | exact (proj2 ADB1) | apply shadow_of_length; lia
        | exact RA1 | rewrite u64_of_Z by lia; lia
        | rewrite u64_of_Z by lia; exact (proj1 (stk_split asegs M1 lo S1 (S1 + 672) ST1 ltac:(lia)))
        | exact ACL | rewrite u64_of_Z by lia; unfold AFREE_STACK; lia
        | exact ERR1 | exact MI1 | exact TPV | rewrite u64_of_Z by lia; exact SP16
        | exact AC1 | exact CHN1
        | rewrite u64_of_Z by (unfold R_DRET; lia); exact TRK
        | reflexivity ]. }
    intros [msF2 mo2] POST.
    destruct POST as (t0' & t1' & t2' & a0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m2 & s'
                      & VIS2 & KR2 & MP2 & MI2 & ST2 & ERR2 & RA2 & AP2 & RH2 & AC2 & AL2).
    cbn [cfg_ms cfg_model] in VIS2, KR2, MP2.
    rewrite u64_of_Z in ST2, AP2 by lia.
    rewrite (ret_pc_even R_DRET ltac:(unfold R_DRET; lia) eq_refl) in VIS2.
    rewrite (proj1 (rt_bp_cost H HHB)) in AL2.
    pose proof (ah_lb_remove H HH) as (LR1 & LR2 & LR3).
    assert (LRE : as_lb_remove H qb ((pid, p, 8 * n) :: LB) = (pid, p, 8 * n) :: as_lb_remove H qb LB) by (apply LR2; cbn; exact Hqp).
    rewrite LRE in AP2, RH2.
    pose proof (lb_remove_perm_app H HH _ _ LBn qb bl (8 * bc) NDL PE1) as PE2. rewrite LRE, <- app_assoc in PE2. cbn [app] in PE2.
    assert (INC2 : forall b, In b (LB0 ++ (pid, p, 8 * n) :: (qn, pn, 32) :: LBn) -> In b ((pid, p, 8 * n) :: as_lb_remove H qb LB))
      by (intros b Hb; exact (Permutation_in _ (Permutation_sym PE2) Hb)).
    assert (XPA : xpres H ((pid, p, 8 * n) :: as_lb_remove H qb LB) S1 [] M1 m2) by exact (xpres_of_apres H _ _ [] _ _ AP2).
    assert (CRS : forall a k, S1 <= a -> aclient_range H ((pid, p, 8 * n) :: as_lb_remove H qb LB) S1 a k) by (intros a k Ha; left; exact Ha).
    assert (CRO : aclient_range H ((pid, p, 8 * n) :: as_lb_remove H qb LB) S1 obj 40).
    { right; right; right; right; left. clear - OB1 OB2. lia. }
    assert (ST2' : stk asegs m2 lo (S1 + 672)).
    { apply (stk_merge asegs m2 lo S1 (S1 + 672)); [exact ST2 | | lia].
      eapply (apres_stk H); [exact AP2 | exact (proj2 (stk_split asegs M1 lo S1 (S1 + 672) ST1 ltac:(lia))) | lia]. }
    assert (WS2 : WSLOTS ty enc S1 obj m2 (Z_to_bv 64 0) (Z_to_bv 64 (pn / 8 + SHBASE))).
    { unfold WSLOTS, nt_wslots. split; [|split; [|split]]; (eapply (apres_rw_cells H); [exact AP2 | | apply CRS; lia]).
      - exact W584M.
      - eapply rw_cells_transport; [exact W600 | exact MU1 | exact WM1 | cbn; lia].
      - eapply rw_cells_transport; [exact W632 | exact MU1 | exact WM1 | cbn; lia].
      - eapply rw_cells_transport; [exact W656 | exact MU1 | exact WM1 | cbn; lia]. }
    assert (NS2 : nt_slots m2 S1 obj v408 v576 v624).
    { unfold nt_slots. repeat match goal with |- _ /\ _ => split end;
        (eapply (apres_rw_cells H); [exact AP2 | eapply rw_cells_transport; [eassumption | exact MU1 | exact WM1 | cbn; lia] | apply CRS; lia]). }
    assert (NODES2 : forall e, In e ents -> agree_on m0 m2 (addr e) 32).
    { intros e He. destruct (ENT e He) as (q & Hq & E0 & EI & EC & EO).
      eapply agree_on_trans; [eapply agree_on_trans; [exact (NODES e He) | apply HIN; lia] |].
      apply (AGA _ _ _ _ _ _ AP2); [| lia | lia]. right; right; left. exists (q, addr e, 32).
      split; [apply INC2; apply in_or_app; right; right; right; exact Hq | cbn; lia]. }
    assert (HDR2 : agree_on m0 m2 (obj + 16) 24).
    { eapply agree_on_trans; [eapply agree_on_trans; [eapply agree_on_sub; [exact HDR | lia | lia] | apply HIN; lia] |].
      apply (AGA _ _ _ _ _ _ AP2); [| lia | lia]. right; right; right; right; left. clear - OB1 OB2. lia. }
    assert (Cbl2 : cell8 ASEGS m2 obj p).
    { eapply cellw_agree; [exact Cbl1 | apply (AGA _ _ _ _ _ _ AP2); [| lia | cbn; lia] | lia | cbn; lia].
      right; right; right; right; left. clear - OB1 OB2. cbn. lia. }
    assert (PBLK1 : rw_cells asegs M1 p [CB (Z.to_nat (8 * n)) junk]).
    { eapply rw_cells_transport; [exact PBLK | exact MU1 | exact WM1 |]. cbn [disjoint_from cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia. lia. }
    assert (PBLK2 : rw_cells asegs m2 p [CB (Z.to_nat (8 * n)) junk]).
    { eapply (apres_rw_cells H); [exact AP2 | exact PBLK1 |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by lia.
      right; right; left. exists (pid, p, 8 * n). split; [left; reflexivity | cbn; lia]. }
    assert (ADP2 : addressable m2 p (8 * n)).
    { eapply (apres_addressable H); [exact AP2 | eapply addressable_transport; [exact ADP | exact MU1 | exact WM1 | apply DSH; lia] | left; reflexivity]. }
    assert (ADN2 : forall e, In e ents -> addressable m2 (addr e) 32).
    { intros e He. destruct (ENT e He) as (q & Hq & E0 & EI & EC & EO).
      eapply (apres_addressable H); [exact AP2 | eapply addressable_transport; [exact (ADN e He) | exact MU1 | exact WM1 | apply DSH; lia] |].
      apply INC2. apply in_or_app. right. right. right. exact Hq. }
    assert (ADH2 : addressable m2 obj 40).
    { assert (ADH1 : addressable M1 obj 40) by (eapply addressable_transport; [exact ADH | exact MU1 | exact WM1 | apply DSH; lia]).
      destruct ADH1 as [Hn40 SH40]. split; [exact Hn40|]. eapply (apres_SHAD H); [exact AP2 | exact SH40 |].
      rewrite shadow_of_length by lia. right; right; right; right; right; left.
      unfold sh, nsh. rewrite ASHADOW_BASE_val. clear - OB1 OB2 Hoal FB3. Z.div_mod_to_equations. lia. }
    assert (WRH2 : wr_at asegs m2 obj 40).
    { eapply xpres_wr_at; [exact XPA | exact (wr_at_wmono _ _ _ _ WRH WM1) |]. split; [exact CRO | apply Forall_nil]. }
    assert (RF2 : as_RFS H LF m2) by exact (RFS_via_apres H HH LF _ _ M1 m2 RF1 AP2).
    assert (S02 : stack0 m2 lo shi) by (eapply (stack0_xpres H); [exact XPA | exact S01 | apply Forall_nil]).
    assert (XP1 : xpres H LB0 S1 (nt_X S1 obj) m M1).
    { eapply (xpres_weaken H); [eapply (xpres_of_munch H s ((pid, p, 8 * n) :: LB) S1 (nt_X S1 obj) [(obj, obj + 8); (S1 + 584, S1 + 592)] m m M1 HH RH MU1 WM1) | lia | |].
      - apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; left; lia|].
        apply Forall_cons; [right; intros a Ha; cbn in Ha |- *; right; left; lia | apply Forall_nil].
      - intros b Hb. right. apply (Permutation_in _ (Permutation_sym PE)). apply in_or_app. left. exact Hb.
      - intros a Ha. exact Ha. }
    assert (XP2 : xpres H LB0 S1 (nt_X S1 obj) m0 m2).
    { eapply xpres_trans; [eapply xpres_trans; [exact XP | exact XP1] |].
      eapply (xpres_weaken H); [exact XPA | lia | intros b Hb; apply INC2; apply in_or_app; left; exact Hb | intros a Ha; destruct Ha]. }
    assert (OWN2 : lb_own ((pid, p, 8 * n) :: (qn, pn, 32) :: LBn) m2).
    { apply lb_own_cons; [cbn [blk_addr blk_size Datatypes.fst Datatypes.snd]; exact (own_of_rw_cells _ _ _ _ PBLK2 ltac:(lia))|].
      eapply (lb_own_apres H); [| exact AP2 |].
      - eapply lb_own_wmono; [| exact WM1]. eapply lb_own_incl; [| exact OWN].
        intros b Hb. destruct Hb as [Hb|Hb]; [left; exact Hb | right; apply (Permutation_in _ (Permutation_sym PS)); right; exact Hb].
      - intros b Hb. apply INC2. apply in_or_app. right. right. exact Hb. }
    assert (NC2 : rw_cells asegs m2 pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)]).
    { eapply (apres_rw_cells H); [exact AP2 | eapply rw_cells_transport; [exact NC | exact MU1 | exact WM1 | cbn; lia] |].
      cbn [cells_size csize Z.of_nat]. right; right; left. exists (qn, pn, 32).
      split; [apply INC2; apply in_or_app; right; right; left; reflexivity | cbn; lia]. }
    assert (ADPN2 : addressable m2 pn 32).
    { eapply (apres_addressable H); [exact AP2 | eapply addressable_transport; [exact ADPN | exact MU1 | exact WM1 | apply DSH; lia] |].
      apply INC2. apply in_or_app. right. right. left. reflexivity. }
    lazymatch type of VIS2 with _ = MS ?RR _ _ _ _ _ _ => remember RR as R2 eqn:HR20 end.
    assert (FHF2 : rfull R2) by (rewrite HR20; apply rfull_mkR).
    pose (E2 := Eseed R2 [Z_to_bv 64 S1; Z_to_bv 64 obj]).
    assert (HR2 : regs_ok E2 (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32)]) R2).
    { apply regs_ok_srs; [apply regs_ok_seed|].
      repeat (apply Forall_cons; [cbn [fst snd]; split; [intros X; discriminate X | subst R2; evs; reflexivity] |]). apply Forall_nil. }
    pose proof WS2 as WS2c. destruct WS2c as (W5842 & W6002 & W6322 & W6562).
    assert (HK2 : know_ok asegs E2 m2 (kn_fix 20 [R_JN] (SCR [] [] []) R_DRET (srs sr_id [(2%bv, EVar 32); (9%bv, EVar 32)])
        [KWord (SA (EVar 32) 584) 8 (ELit 0); KWord (SA (EVar 32) 656) 8 (EVar 33); KRange (EVar 32) (2 ^ 45) (2 ^ 47 - 672)] 50)).
    { kn_eval. unfold know_ok.
      apply Forall_cons; [kword_cell W5842 0%nat (C8 (Z_to_bv 64 0))|].
      apply Forall_cons; [kword_cell W6562 0%nat (C8 (Z_to_bv 64 obj))|].
      apply Forall_cons; [cbn [kentry_ok]; evs; rewrite u64_of_Z by lia; lia|].
      know_tac. }
    xrun_at (PropExec.mkFP F fc) asegs R2 R_DRET m2 (seg_rom asegs) HR2 HK2 20%nat [R_JN] (SCR [] [] []) 50%N.
    { split_scs. }
    clear HK2.
    readback HR' (msteps_full asegs _ _ Hms FHF2) HR20 HRe2.
    rreg HR' 2%bv K2. rreg HR' 9%bv K9. rreg HR' 13%bv K13. rreg HR' 25%bv K25. rreg HR' 30%bv K30. rreg HR' 31%bv K31.
    assert (K30' : getr R' 30 = LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) by (rewrite K30, HR20; reflexivity).
    assert (K31' : getr R' 31 = Z_to_bv 64 (2 ^ 60)) by (rewrite K31, HR20; reflexivity).
    rewrite K2, K9, K13, K25, K30', K31' in HRe2.
    eapply (sr_blk_eq H HH); [exact KR2 | exact VIS2 | exact FHF2 | exact Hms | exact HRe2 |].
    intros msF3 mo3 KR3 MP3 VIS3.
    eapply (stage_c s' msF3 mo3 m2 F fc _ _ _ _ _ _ _ _ _ _ _ _ _ _ errv ((pid, p, 8 * n) :: as_lb_remove H qb LB) LBn pid qn p pn junk (Z_to_bv 64 0));
      [ exact VIS3 | exact FRZ | exact KR3
      | eapply (ah_mpres_trans H HH); [exact MP | eapply (ah_mpres_trans H HH); [exact MP1 | eapply (ah_mpres_trans H HH); [exact MP2 | exact MP3]]]
      | exact WS2 | exact NS2 | exact SPL | exact SPH | exact V64 | exact MI2 | exact ST2' | exact ERR2 | exact RA2
      | exact NODES2 | exact HDR2 | exact Cbl2 | exact PBLK2 | exact ADP2 | exact ADH2 | exact ADN2 | exact WRH2
      | exact RH2 | exact PE2 | exact PMn | exact OWN2 | exact XP2 | exact RF2 | exact AC2 | exact S02 | clear - AL AL2; lia
      | exact NC2 | exact ADPN2 | exact GROW ].
  Qed.

  Lemma stage_b : forall (s : as_St H) (msF : machine_state) (mo : Model) (m : mem) (F : bvmap 5 word) (fc : bv 32)
      (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y19 y28 y29 y30 y31 : word) (errv : word) (LB LBm : list block) (pid qn : bptr) (p pn : Z)
      (junk : list byte) (j584 : word),
    as_VIS H s msF = MS (mkR (Z_to_bv 64 R_NEWRET) (Z_to_bv 64 S1) gp tp y5 y6 y7 s0 (Z_to_bv 64 S1) (Z_to_bv 64 p) y11 y12 y13 y14 y15 y16 y17
                             (Z_to_bv 64 key) y19 s4 (LbB_NtD.rShe (Z_to_bv 64 (obj + 24))) (Z_to_bv 64 (2 ^ 60)) (Z_to_bv 64 pn) wd
                             (Z_to_bv 64 obj) (Z_to_bv 64 (obj + 24)) (Z_to_bv 64 n) y28 y29 y30 y31)
                        F (Z_to_bv 64 R_NEWRET) fc None m (seg_rom asegs) ->
    frm_zero fc -> as_AKREL H s (mkCfg msF mo) -> as_MPRES H mo0 mo ->
    WSLOTS ty enc S1 obj m j584 (Z_to_bv 64 (pn / 8 + SHBASE)) -> nt_slots m S1 obj v408 v576 v624 ->
    2 ^ 45 <= S1 -> S1 + 672 <= 2 ^ 47 -> (0 <= v408 < 2 ^ 64 /\ 0 <= v576 < 2 ^ 64 /\ 0 <= v624 < 2 ^ 64) ->
    mem_inv asegs m -> stk asegs m lo (S1 + 672) -> rw_cells asegs m (errno_addr tp) [C4 errv] -> as_rauxv_ok H m B ->
    (forall e, In e ents -> agree_on m0 m (addr e) 32) -> agree_on m0 m obj 40 ->
    (bc <> 0 -> addressable m bl (8 * bc)) -> addressable m obj 40 -> (forall e, In e ents -> addressable m (addr e) 32) ->
    wr_at asegs m obj 40 ->
    as_RHEAP H s ((pid, p, 8 * n) :: LB) m ->
    Permutation LB (LB0 ++ (qn, pn, 32) :: LBm) -> Permutation (lbl LBm) (umap_blocks 32 bl bc ents) -> lb_own ((qn, pn, 32) :: LBm) m ->
    rw_cells asegs m p [CB (Z.to_nat (8 * n)) junk] -> addressable m p (8 * n) ->
    xpres H LB0 S1 (nt_X S1 obj) m0 m -> as_RFS H LF m -> ACONST m -> stack0 m lo shi ->
    as_AL H s >= as_AL H sk0 - ICM (8 * n) ->
    rw_cells asegs m pn [C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 key); C4 (Z_to_bv 64 key); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0); C4 (Z_to_bv 64 0)] ->
    addressable m pn 32 -> (bc = 0 \/ Zlength ents = bc) ->
    as_chain H m (bv_unsigned s0) CH ->
    as_SR H QIx (mkCfg msF mo).
  Proof using HHB U0 Hlast AL0 OCE LFO ACL LOS LOR TPV KR32 ZLEN SP16 SPB TRK CHH.
    intros. destruct (Z.eq_dec bc 0) as [Hz | Hnz].
    - eapply stage_b_z; eassumption.
    - eapply stage_b_nz; eassumption.
  Qed.
End NtRB.
