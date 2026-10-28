(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatSim SymExec3 SymExec3Sound SymRun3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibTabl Require Import TablLib TablRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BMState BMem BCells BExec BLFrame BStep BSysStep BacX BellsX HWord.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BsWalk RtB_Iface RtB_StrcmpStmt.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_Kit LbB_Bridge LbB_Call LbB_Conv.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LbB_TablStmt LbB_TablImg.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Definition ITG_RET : Z := 0x1004c8.

Definition ITG_LITS : list (Z * Z) := [(0x62460, 12); (0x62480, 10); (0x624a0, 40); (0x62500, 29); (0x62540, 18); (0x62580, 21); (0x625c0, 9); (0x625e0, 20); (0x62620, 29); (0x62660, 28); (0x626a0, 28); (0x626e0, 27); (0x62720, 13); (0x62740, 20); (0x62780, 29); (0x627c0, 12)].

Definition itg_lits_okb : bool :=
  forallb (fun pn => chk_cstr ASEGS tiA (fst pn) (snd pn)
                     && existsb (fun g => let '(b, sz, _) := g in (b =? fst pn) && (sz =? snd pn + 1)) aglobals
                     && (0x10040 <=? fst pn) && (fst pn + snd pn + 1 <=? 0x63000)) ITG_LITS.
Lemma itg_lits_ok : itg_lits_okb = true.
Proof. vm_compute. reflexivity. Qed.

Lemma itg_lit : forall p n, In (p, n) ITG_LITS -> cstrA p n /\ p + n + 1 <= 0x63000.
Proof.
  intros p n Hin. pose proof itg_lits_ok as K. unfold itg_lits_okb in K. rewrite forallb_forall in K.
  specialize (K _ Hin). cbn [fst snd] in K. apply andb_prop in K as [K LOW]. apply andb_prop in K as [K B]. apply andb_prop in K as [C G].
  apply existsb_exists in G as ([[b sz] rz] & Hg & E). apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1, E2. subst b sz.
  apply Z.leb_le in B. apply Z.leb_le in LOW.
  split; [eapply (cstrA_of p n p (n + 1) rz C Hg); lia | exact LOW].
Qed.

Ltac in_lits := cbn; repeat (first [left; reflexivity | right]).

Lemma b8_unsigned : forall (x : byte), b8 (bv_unsigned x) = x.
Proof. intros x. unfold b8. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range. Qed.

Lemma map_b8_unsigned : forall (l : list byte), map b8 (map bv_unsigned l) = l.
Proof. induction l as [|x l IH]; [reflexivity|]. cbn [map]. rewrite IH, b8_unsigned. reflexivity. Qed.

Lemma nonnul_range : forall (l : list byte), ~ In (Z_to_bv 8 0) l -> Forall (fun c => 0 < c < 256) (map bv_unsigned l).
Proof.
  induction l as [|x l IH]; intros NI; [apply Forall_nil|]. cbn [map]. apply Forall_cons.
  - pose proof (bv_unsigned_in_range 8 x) as R. unfold bv_modulus in R. change (2 ^ Z.of_N 8) with 256 in R.
    destruct (Z.eq_dec (bv_unsigned x) 0) as [E|NE]; [|lia]. exfalso. apply NI. left.
    rewrite <- (b8_unsigned x). rewrite E. reflexivity.
  - apply IH. intros X. apply NI. right. exact X.
Qed.

Lemma cstr_icpt : forall p n m, cstrA p n -> mem_inv asegs m -> ACONST m ->
  exists (e : list Z),
    bytes_at asegs m p (map b8 (e ++ 0 :: [])) /\ Forall (fun c => 0 < c < 256) e /\ Z.of_nat (length e) = n
    /\ accessible m p (n + 1) /\ shvis m p (p + n + 1) /\ in_app_mem p (p + n + 1) /\ 0 <= p /\ 0 <= n <= 256.
Proof.
  intros p n m (P1 & N1 & P2 & IA & AS & CS) MI AC.
  destruct (AS m AC) as [ACC SV]. destruct (CS m MI) as (str & slack & BA & LEN & NI & SL).
  exists (map bv_unsigned str).
  change (str ++ Z_to_bv 8 0 :: slack) with (str ++ ([Z_to_bv 8 0] ++ slack)) in BA. rewrite app_assoc in BA.
  apply bytes_at_app in BA as [BA _].
  split; [rewrite map_app; cbn [map]; rewrite map_b8_unsigned; unfold b8; exact BA|].
  split; [exact (nonnul_range str NI)|]. split; [rewrite length_map; exact LEN|].
  split; [exact ACC|]. split; [exact SV|]. split; [exact IA|]. unfold AIMG_LO in P1. lia.
Qed.

Lemma bytes_at_munch : forall W m m' a (bs : list byte),
  bytes_at asegs m a bs -> munch W m m' -> disjoint_from W a (Z.of_nat (length bs)) -> bytes_at asegs m' a bs.
Proof.
  intros W m m' a bs (B0 & B1 & B) MU D. split; [exact B0|]. split; [exact B1|].
  intros i Hi. unfold mrd. unfold wa. rewrite (MU (Z_to_bv 64 (a + Z.of_nat i))); [apply B; exact Hi|].
  rewrite HLib.u64_of_Z by lia. eapply disjoint_outside; [exact D | lia].
Qed.

Ltac itg_norun_fin :=
  lazymatch goal with
  | Hms : CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _), HR' : regs_ok _ _ ?R',
    HR0 : ?R = mkR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
      cbn [mem_denot] in Hms;
      let HF := fresh "HF" in assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR);
      let HF1 := fresh "HF1" in pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1;
      let HRe := fresh "HRe" in readback HR' HF1 HR0 HRe;
      rewrite HRe in Hms
  end.

Ltac ms_close Hms :=
  lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ ?R ?pc ?mm _) =>
    lazymatch goal with |- CatSim.msteps _ _ (MS ?R' _ ?pc' _ _ ?mm' _) =>
      replace R' with R; [replace pc' with pc; [replace mm' with mm; [exact Hms|]|]|] end end;
  repeat (first [reflexivity | progress f_equal]);
  try lia; try (apply bv_eq; vm_compute; reflexivity).

Section ITGruns.
  Context {HCEIL : HeapCeil}.

  Lemma itg_r0 : forall (ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q lo : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> 0 <= q < 2 ^ 64 ->
    stk asegs m lo SP -> lo <= SP - 16 -> mem_inv asegs m ->
    exists M',
      CatSim.msteps asegs
        (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 AT_IMPORT_TYPE_GET) fc None m ro)
        (MS (mkR (Z_to_bv 64 0x100370) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62460) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None M' ro)
      /\ munch [(SP - 16, SP)] m M' /\ wmono asegs m M' /\ mem_inv asegs M'
      /\ (forall lo' hi', stk asegs m lo' hi' -> stk asegs M' lo' hi')
      /\ rw_cells asegs M' (SP - 16) [C8 s0; C8 ra].
  Proof.
    intros until lo. intros SPR QR ST LO MI.
    remember (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 q) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 SP; Z_to_bv 64 q]).
    assert (HR : regs_ok E (srs sr_id [(2%bv, EVar 32); (10%bv, EVar 33)]) R).
    { apply regs_ok_srs; [apply regs_ok_seed|]. repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity. }
    assert (HB : bv_unsigned (edenot E (EVar 32)) = SP) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWr (SA (EVar 32) (-16)) (ELit 16); KRange (EVar 32) (2 ^ 45) (2 ^ 47 + 1); KRange (EVar 33) 0 (2 ^ 64) ]).
    { unfold know_ok.
      apply Forall_cons.
      { eapply kwr_of_stk; [exact ST | unfold estart; cbn [a_base a_off]; rewrite HB; lia
                           | unfold estart, elenZ; cbn [a_base a_off]; rewrite HB; subst E R; evs; rewrite u64_of_Z by lia; lia
                           | unfold elenZ; subst E R; evs; rewrite u64_of_Z by lia; lia]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite HB; lia|].
      apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; rewrite u64_of_Z by lia; lia | apply Forall_nil]. }
    assert (WS : forall a, SP - 16 <= a -> a + 8 <= SP -> wr_at asegs m a 8).
    { intros a X1 X2. pose proof (wr_at_of_stk asegs m lo SP ST) as W. destruct W as (W1 & W2 & W).
      split; [lia|]. split; [lia|]. intros i Hi. replace (a + i) with (lo + (a - lo + i)) by lia. apply W. lia. }
    xrun_at (PropExec.mkFP F fc) asegs R AT_IMPORT_TYPE_GET m ro HR HK 20%nat [ASTRCMP_STUB] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    clear HK.
    lazymatch type of Hlf with log_flat _ ?lg =>
      lazymatch type of Hms with CatSim.msteps _ _ (@PropExec.mkst _ _ _ ?mm _) =>
        change mm with (mem_denot E m lg) in Hms; set (M1 := mem_denot E m lg) in Hms end end.
    exists M1.
    assert (HF : rfull R) by (rewrite HR0; apply rfull_mkR).
    pose proof (msteps_full asegs _ _ Hms HF) as HF1; cbn [ms_regs] in HF1.
    readback HR' HF1 HR0 HRe.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    split.
    { rewrite HRe in Hms. rewrite L1, L2, L8, L10, L11 in Hms. try subst E. revert Hms. subst R. evs.
      rewrite ?w_add, ?w_addm by lia. intros Hms.
      ms_close Hms. }
    split.
    { subst M1. clear - Hlf HB SPR.
      pose proof (munch_mem_denot_sb [(-16, 0)] (EVar 32) _ m _ Hlf ltac:(vm_compute; reflexivity)) as MU.
      rewrite HB in MU. cbn [map fst snd] in MU. eapply munch_eqW; [exact MU | repeat f_equal; lia]. }
    split; [subst M1; apply wmono_mem_denot|]. split; [exact (msteps_mem_inv asegs _ _ Hms MI)|].
    split; [intros lo' hi' S; subst M1; apply stk_mem_denot; exact S|].
    subst M1. clear - Hlf HB SPR WS HR0.
    apply rw_cells_cons8_c; [lgcell2 Hlf HB WS 0%nat | lgcell2 Hlf HB WS 1%nat].
  Qed.

  Lemma itg_nz1 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100370) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100370) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x100384) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62480) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x100370) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x100370 m ro HR HK 12%nat [ASTRCMP_STUB; 0x1004cc] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz2 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100384) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100384) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x100398) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x624a0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x100384) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x100384 m ro HR HK 12%nat [ASTRCMP_STUB; 0x1004e0] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz3 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100398) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100398) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x1003ac) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62500) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x100398) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x100398 m ro HR HK 12%nat [ASTRCMP_STUB; 0x1004f4] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz4 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003ac) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003ac) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x1003c0) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62540) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x1003ac) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003ac m ro HR HK 12%nat [ASTRCMP_STUB; 0x100508] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz5 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003c0) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003c0) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x1003d4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62580) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x1003c0) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003c0 m ro HR HK 12%nat [ASTRCMP_STUB; 0x10051c] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz6 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003d4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003d4) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x1003e8) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x625c0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x1003d4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003d4 m ro HR HK 12%nat [ASTRCMP_STUB; 0x100530] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz7 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003e8) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003e8) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x1003fc) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x625e0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x1003e8) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003e8 m ro HR HK 12%nat [ASTRCMP_STUB; 0x100544] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz8 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003fc) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003fc) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x100414) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62620) (Z_to_bv 64 q) (Z_to_bv 64 29) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x1003fc) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003fc m ro HR HK 12%nat [ASTRNCMP_STUB; 0x100558] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rewrite L1, L10, L11, L12 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz9 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100414) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100414) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x10042c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62660) (Z_to_bv 64 q) (Z_to_bv 64 28) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x100414) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x100414 m ro HR HK 12%nat [ASTRNCMP_STUB; 0x10056c] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rewrite L1, L10, L11, L12 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz10 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x10042c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10042c) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x100444) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x626a0) (Z_to_bv 64 q) (Z_to_bv 64 28) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x10042c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x10042c m ro HR HK 12%nat [ASTRNCMP_STUB; 0x100580] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rewrite L1, L10, L11, L12 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz11 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100444) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100444) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x10045c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x626e0) (Z_to_bv 64 q) (Z_to_bv 64 27) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x100444) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x100444 m ro HR HK 12%nat [ASTRNCMP_STUB; 0x100594] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rewrite L1, L10, L11, L12 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz12 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x10045c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10045c) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x100470) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62720) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x10045c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x10045c m ro HR HK 12%nat [ASTRCMP_STUB; 0x1005a8] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz13 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100470) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100470) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x100484) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62740) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x100470) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x100470 m ro HR HK 12%nat [ASTRCMP_STUB; 0x1005bc] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11.
    rewrite L1, L10, L11 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz14 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100484) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100484) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x10049c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62780) (Z_to_bv 64 q) (Z_to_bv 64 29) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x100484) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x100484 m ro HR HK 12%nat [ASTRNCMP_STUB; 0x1005d0] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rewrite L1, L10, L11, L12 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_nz15 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x10049c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10049c) fc None m ro)
      (MS (mkR (Z_to_bv 64 0x1004b4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x627c0) (Z_to_bv 64 q) (Z_to_bv 64 12) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None m ro).
  Proof.
    intros until q. intros XNZ.
    remember (mkR (Z_to_bv 64 0x10049c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [KRange (EVar 32) 1 (2 ^ 64)]) by (apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia | apply Forall_nil]).
    xrun_at (PropExec.mkFP F fc) asegs R 0x10049c m ro HR HK 12%nat [ASTRNCMP_STUB; 0x1005e4] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 10%bv L10. rreg HR' 11%bv L11. rreg HR' 12%bv L12.
    rewrite L1, L10, L11, L12 in Hms. try subst E. revert Hms. subst R. evs. intros Hms. exact Hms.
  Qed.

  Lemma itg_z1 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100370) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100370) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 1) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1004dc) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x100370) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x100370 m ro HR HK 12%nat [0x1004dc; 0x100374] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z2 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100384) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100384) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 2) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1004f0) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x100384) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x100384 m ro HR HK 12%nat [0x1004f0; 0x100388] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z3 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100398) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100398) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 3) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100504) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x100398) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x100398 m ro HR HK 12%nat [0x100504; 0x10039c] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z4 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003ac) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003ac) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 4) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100518) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x1003ac) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003ac m ro HR HK 12%nat [0x100518; 0x1003b0] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z5 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003c0) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003c0) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 5) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10052c) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x1003c0) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003c0 m ro HR HK 12%nat [0x10052c; 0x1003c4] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z6 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003d4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003d4) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 6) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100540) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x1003d4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003d4 m ro HR HK 12%nat [0x100540; 0x1003d8] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z7 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003e8) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003e8) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 7) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100554) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x1003e8) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003e8 m ro HR HK 12%nat [0x100554; 0x1003ec] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z8 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1003fc) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1003fc) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 8) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100568) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x1003fc) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x1003fc m ro HR HK 12%nat [0x100568; 0x100400] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z9 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100414) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100414) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 11) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10057c) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x100414) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x100414 m ro HR HK 12%nat [0x10057c; 0x100418] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z10 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x10042c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10042c) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 10) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100590) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x10042c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x10042c m ro HR HK 12%nat [0x100590; 0x100430] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z11 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100444) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100444) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 9) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1005a4) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x100444) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x100444 m ro HR HK 12%nat [0x1005a4; 0x100448] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z12 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x10045c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10045c) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 12) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1005b8) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x10045c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x10045c m ro HR HK 12%nat [0x1005b8; 0x100460] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z13 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100470) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100470) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 13) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1005cc) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x100470) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x100470 m ro HR HK 12%nat [0x1005cc; 0x100474] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z14 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x100484) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x100484) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 14) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1005e0) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x100484) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x100484 m ro HR HK 12%nat [0x1005e0; 0x100488] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_z15 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x10049c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x10049c) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 15) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1005f4) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x10049c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia | apply Forall_nil]. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x10049c m ro HR HK 12%nat [0x1005f4; 0x1004a0] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_f0 : forall (gp tp t0 t1 t2 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1004b4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1004b4) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 16) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ITG_RET) fc None m ro).
  Proof.
    intros until q. intros SPR CS.
    remember (mkR (Z_to_bv 64 0x1004b4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, ELit 0); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia |].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x1004b4 m ro HR HK 12%nat [ITG_RET] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.

  Lemma itg_f1 : forall (gp tp t0 t1 t2 s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (rao s0o : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (ro : word -> option byte) (SP q : Z),
    2 ^ 45 <= SP <= 2 ^ 47 -> rw_cells asegs m (SP - 16) [C8 s0o; C8 rao] -> bv_unsigned x <> 0 ->
    CatSim.msteps asegs
      (MS (mkR (Z_to_bv 64 0x1004b4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 0x1004b4) fc None m ro)
      (MS (mkR rao (Z_to_bv 64 SP) gp tp t0 t1 t2 s0o s1 (Z_to_bv 64 0) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ITG_RET) fc None m ro).
  Proof.
    intros until q. intros SPR CS XNZ.
    remember (mkR (Z_to_bv 64 0x1004b4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 x a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) as R eqn:HR0.
    pose (E := Eseed R [Z_to_bv 64 (SP - 16); s0o; rao; x]).
    assert (HR : regs_ok E (srs sr_id [(10%bv, EVar 35); (2%bv, EVar 32)]) R)
      by (apply regs_ok_srs; [apply regs_ok_seed|]; repeat constructor; cbn [fst snd]; try (intros X; discriminate X); subst R; evs; reflexivity).
    assert (EP : bv_unsigned (edenot E (EVar 32)) = SP - 16) by (subst E R; evs; rewrite u64_of_Z by lia; reflexivity).
    pose proof (bv_unsigned_in_range 64 x) as XR. change (bv_modulus 64) with (2 ^ 64) in XR.
    assert (HK : know_ok asegs E m [ KWord (SA (EVar 32) 0) 8 (EVar 33); KWord (SA (EVar 32) 8) 8 (EVar 34); KRange (EVar 32) (2 ^ 44) (2 ^ 47); KRange (EVar 35) 1 (2 ^ 64) ]).
    { unfold know_ok.
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 0%nat (C8 s0o)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons. { eapply (kword_of_rw_cells asegs _ _ _ _ 8%nat (C8 rao)); [exact CS | reflexivity | reflexivity | lia
          | unfold estart; cbn [a_base a_off]; rewrite EP; cbn; lia | cbn; lia | cbn; lia | subst E R; HLib.evs; reflexivity]. }
      apply Forall_cons; [cbn [kentry_ok]; rewrite EP; lia |].
      apply Forall_cons; [cbn [kentry_ok]; subst E R; evs; lia |].
      apply Forall_nil. }
    xrun_at (PropExec.mkFP F fc) asegs R 0x1004b4 m ro HR HK 12%nat [ITG_RET] (SCR [] [] []) 40%N.
    { first [apply Forall_nil | split_scs]. }
    itg_norun_fin.
    rreg HR' 1%bv L1. rreg HR' 2%bv L2. rreg HR' 8%bv L8. rreg HR' 10%bv L10.
    rewrite L1, L2, L8, L10 in Hms. try subst E. revert Hms. subst R. evs. rewrite ?w_add, ?w_addm by lia. intros Hms.
    ms_close Hms.
  Qed.
End ITGruns.

Section ITGsites.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.
  Hypothesis SC : strcmp_icpt_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (str : list byte) (SP q lo : Z).

  Definition itg_pre : Prop :=
    bytes_at asegs m q (str ++ [Z_to_bv 8 0]) /\ ~ In (Z_to_bv 8 0) str
    /\ accessible m q (Z.of_nat (length str) + 1) /\ shvis m q (q + Z.of_nat (length str) + 1)
    /\ in_app_mem q (q + Z.of_nat (length str) + 1) /\ Z.of_nat (length str) + 1 <= 2 ^ 40
    /\ (q + Z.of_nat (length str) + 1 <= lo \/ SP <= q)
    /\ aceil <= lo /\ lo <= SP - IT_STACK /\ SP <= 2 ^ 47 /\ 0 <= q < 2 ^ 64.
  Hypothesis PRE : itg_pre.

  Definition itg_G (mk : mem) : Prop :=
    munch [(SP - IT_STACK, SP)] m mk /\ wmono asegs m mk /\ mem_inv asegs mk /\ stk asegs mk lo SP /\ ACONST mk
    /\ rw_cells asegs mk (SP - 16) [C8 s0; C8 ra].

  Definition itg_Q : machine_state -> Prop :=
    tl_post ra (Z_to_bv 64 SP) gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc IT_STACK [] lo m
            (fun r0 _ _ => exists r, 0 <= r < 2 ^ 31 /\ r0 = Z_to_bv 64 r).

  Lemma itg_geo : 2 ^ 45 + IT_STACK <= SP <= 2 ^ 47 /\ 0x7fff7f800000 <= lo /\ lo <= SP - IT_STACK /\ 0 <= q < 2 ^ 64 /\ IT_STACK = 16 + 4096 /\ aceil <= lo.
  Proof.
    destruct PRE as (_ & _ & _ & _ & _ & _ & _ & CE & LO & S47 & QR).
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4). unfold IT_STACK, AINTRIN_STACK in *. lia.
  Qed.

  Lemma itg_Gstep : forall mk m1, itg_G mk ->
    munch [(SP - 16 - AINTRIN_STACK, SP - 16)] mk m1 -> wmono asegs mk m1 -> mem_inv asegs m1 -> stk asegs m1 lo (SP - 16) -> ACONST m1 ->
    itg_G m1.
  Proof.
    intros mk m1 (MU & WM & MI & ST & AC & CS) MU1 WM1 MI1 ST1 AC1. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6).
    unfold itg_G. unfold IT_STACK, AINTRIN_STACK in *.
    split.
    { eapply munch_trans; [exact MU|]. eapply munch_weaken; [|exact MU1]. intros z Hz. cbn [outside] in Hz |- *. lia. }
    split; [exact (wmono_trans _ _ _ _ WM WM1)|]. split; [exact MI1|].
    split.
    { destruct (stk_split asegs mk lo (SP - 16) SP ST ltac:(lia)) as [_ STu].
      assert (STu1 : stk asegs m1 (SP - 16) SP) by (eapply stk_transport_disjoint; [exact STu | exact MU1 | exact WM1 | cbn; lia]).
      exact (stk_merge asegs m1 lo (SP - 16) SP ST1 STu1 ltac:(lia)). }
    split; [exact AC1|].
    eapply rw_cells_transport; [exact CS | exact MU1 | exact WM1 | cbn; lia].
  Qed.

  Lemma itg_client : forall mk, itg_G mk ->
    bytes_at asegs mk q (map b8 (map bv_unsigned str ++ 0 :: [])) /\ Forall (fun c => 0 < c < 256) (map bv_unsigned str)
    /\ Z.of_nat (length (map bv_unsigned str)) = Z.of_nat (length str)
    /\ accessible mk q (Z.of_nat (length str) + 1) /\ shvis mk q (q + Z.of_nat (length str) + 1).
  Proof.
    intros mk (MU & WM & MI & ST & AC & CS). pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct PRE as (BA & NI & ACC & SV & IA & L40 & QLO & _).
    assert (WH : wins_hi [(SP - IT_STACK, SP)]) by (apply Forall_cons; [right; cbn [fst]; unfold AHI_LO, IT_STACK, AINTRIN_STACK; lia | apply Forall_nil]).
    split.
    { rewrite map_app. cbn [map]. rewrite map_b8_unsigned. unfold b8.
      eapply bytes_at_munch; [exact BA | exact MU |]. cbn. rewrite length_app. cbn [length]. split; [|exact I]. clear - QLO G3 G5. lia. }
    split; [exact (nonnul_range str NI)|]. split; [rewrite length_map; reflexivity|].
    split; [exact (accessible_transport_hi _ _ _ _ _ ACC MU WH)|].
    eapply shvis_transport_hi; [exact SV | exact MU | exact WM | clear - IA; unfold in_app_mem, AHI_LO, AAPP_HI, ASHADOW_BASE in *; lia
                               | clear - IA; unfold in_app_mem, AHI_LO, AAPP_HI in *; rewrite ?ASHADOW_BASE_val in IA; lia | exact WH].
  Qed.

  Lemma itg_exit : forall m1 (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (r : Z), itg_G m1 -> 0 <= r < 2 ^ 31 ->
    itg_Q (MS (mkR ra (Z_to_bv 64 SP) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
              F (ret_pc ra) fc None m1 (seg_rom asegs)).
  Proof.
    intros until r. intros (MU & WM & MI & ST & AC & CS) Hr. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    unfold itg_Q, tl_post. exists t0, t1, t2, (Z_to_bv 64 r), a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m1.
    rewrite u64_of_Z by lia.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST|]. split; [exact AC|].
    exists r. split; [exact Hr | reflexivity].
  Qed.

  Lemma itg_s16 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x1004b4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x627c0) (Z_to_bv 64 q) (Z_to_bv 64 12) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x627c0 12 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x627c0 12 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply ((ah_strncmp H HB) (Z_to_bv 64 0x1004b4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x627c0) (Z_to_bv 64 q) (Z_to_bv 64 12) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] 12 lo);
        rewrite ?u64_of_Z by lia;
        [ reflexivity | lia | rewrite LE; lia | exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; eapply accessible_sub; [exact ACe | lia | lia | lia]
        | rewrite LT; eapply accessible_sub; [exact ACt | lia | lia | lia]
        | rewrite LE; exact SVe
        | rewrite LT; eapply shvis_sub; [exact SVt | lia | lia | lia | lia | lia]
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia
        | rewrite LE; eapply in_app_mem_sub; [exact IAe | lia | lia]
        | rewrite LT; eapply in_app_mem_sub; [exact IAt | lia | lia]
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & _ & _ & _ & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x1004b4 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_f0 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [exact (itg_f1 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1 NZ)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
  Qed.

  Lemma itg_s15 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x10049c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62780) (Z_to_bv 64 q) (Z_to_bv 64 29) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62780 29 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62780 29 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply ((ah_strncmp H HB) (Z_to_bv 64 0x10049c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62780) (Z_to_bv 64 q) (Z_to_bv 64 29) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] 29 lo);
        rewrite ?u64_of_Z by lia;
        [ reflexivity | lia | rewrite LE; lia | exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; eapply accessible_sub; [exact ACe | lia | lia | lia]
        | rewrite LT; eapply accessible_sub; [exact ACt | lia | lia | lia]
        | rewrite LE; exact SVe
        | rewrite LT; eapply shvis_sub; [exact SVt | lia | lia | lia | lia | lia]
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia
        | rewrite LE; eapply in_app_mem_sub; [exact IAe | lia | lia]
        | rewrite LT; eapply in_app_mem_sub; [exact IAt | lia | lia]
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & _ & _ & _ & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x10049c ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z15 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz15 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s16. exact GG1.
  Qed.

  Lemma itg_s14 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x100484) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62740) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62740 20 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62740 20 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x100484) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62740) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x100484 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z14 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz14 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s15. exact GG1.
  Qed.

  Lemma itg_s13 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x100470) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62720) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62720 13 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62720 13 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x100470) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62720) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x100470 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z13 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz13 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s14. exact GG1.
  Qed.

  Lemma itg_s12 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x10045c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x626e0) (Z_to_bv 64 q) (Z_to_bv 64 27) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x626e0 27 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x626e0 27 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply ((ah_strncmp H HB) (Z_to_bv 64 0x10045c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x626e0) (Z_to_bv 64 q) (Z_to_bv 64 27) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] 27 lo);
        rewrite ?u64_of_Z by lia;
        [ reflexivity | lia | rewrite LE; lia | exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; eapply accessible_sub; [exact ACe | lia | lia | lia]
        | rewrite LT; eapply accessible_sub; [exact ACt | lia | lia | lia]
        | rewrite LE; exact SVe
        | rewrite LT; eapply shvis_sub; [exact SVt | lia | lia | lia | lia | lia]
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia
        | rewrite LE; eapply in_app_mem_sub; [exact IAe | lia | lia]
        | rewrite LT; eapply in_app_mem_sub; [exact IAt | lia | lia]
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & _ & _ & _ & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x10045c ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z12 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz12 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s13. exact GG1.
  Qed.

  Lemma itg_s11 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x100444) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x626a0) (Z_to_bv 64 q) (Z_to_bv 64 28) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x626a0 28 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x626a0 28 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply ((ah_strncmp H HB) (Z_to_bv 64 0x100444) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x626a0) (Z_to_bv 64 q) (Z_to_bv 64 28) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] 28 lo);
        rewrite ?u64_of_Z by lia;
        [ reflexivity | lia | rewrite LE; lia | exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; eapply accessible_sub; [exact ACe | lia | lia | lia]
        | rewrite LT; eapply accessible_sub; [exact ACt | lia | lia | lia]
        | rewrite LE; exact SVe
        | rewrite LT; eapply shvis_sub; [exact SVt | lia | lia | lia | lia | lia]
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia
        | rewrite LE; eapply in_app_mem_sub; [exact IAe | lia | lia]
        | rewrite LT; eapply in_app_mem_sub; [exact IAt | lia | lia]
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & _ & _ & _ & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x100444 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z11 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz11 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s12. exact GG1.
  Qed.

  Lemma itg_s10 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x10042c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62660) (Z_to_bv 64 q) (Z_to_bv 64 28) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62660 28 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62660 28 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply ((ah_strncmp H HB) (Z_to_bv 64 0x10042c) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62660) (Z_to_bv 64 q) (Z_to_bv 64 28) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] 28 lo);
        rewrite ?u64_of_Z by lia;
        [ reflexivity | lia | rewrite LE; lia | exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; eapply accessible_sub; [exact ACe | lia | lia | lia]
        | rewrite LT; eapply accessible_sub; [exact ACt | lia | lia | lia]
        | rewrite LE; exact SVe
        | rewrite LT; eapply shvis_sub; [exact SVt | lia | lia | lia | lia | lia]
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia
        | rewrite LE; eapply in_app_mem_sub; [exact IAe | lia | lia]
        | rewrite LT; eapply in_app_mem_sub; [exact IAt | lia | lia]
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & _ & _ & _ & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x10042c ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z10 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz10 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s11. exact GG1.
  Qed.

  Lemma itg_s9 : forall (t0 t1 t2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x100414) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62620) (Z_to_bv 64 q) (Z_to_bv 64 29) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRNCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62620 29 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62620 29 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply ((ah_strncmp H HB) (Z_to_bv 64 0x100414) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62620) (Z_to_bv 64 q) (Z_to_bv 64 29) a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] 29 lo);
        rewrite ?u64_of_Z by lia;
        [ reflexivity | lia | rewrite LE; lia | exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; eapply accessible_sub; [exact ACe | lia | lia | lia]
        | rewrite LT; eapply accessible_sub; [exact ACt | lia | lia | lia]
        | rewrite LE; exact SVe
        | rewrite LT; eapply shvis_sub; [exact SVt | lia | lia | lia | lia | lia]
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia
        | rewrite LE; eapply in_app_mem_sub; [exact IAe | lia | lia]
        | rewrite LT; eapply in_app_mem_sub; [exact IAt | lia | lia]
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & _ & _ & _ & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x100414 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z9 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz9 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s10. exact GG1.
  Qed.

  Lemma itg_s8 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x1003fc) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x625e0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x625e0 20 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x625e0 20 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x1003fc) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x625e0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x1003fc ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z8 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz8 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s9. exact GG1.
  Qed.

  Lemma itg_s7 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x1003e8) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x625c0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x625c0 9 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x625c0 9 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x1003e8) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x625c0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x1003e8 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z7 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz7 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s8. exact GG1.
  Qed.

  Lemma itg_s6 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x1003d4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62580) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62580 21 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62580 21 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x1003d4) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62580) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x1003d4 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z6 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz6 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s7. exact GG1.
  Qed.

  Lemma itg_s5 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x1003c0) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62540) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62540 18 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62540 18 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x1003c0) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62540) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x1003c0 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z5 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz5 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s6. exact GG1.
  Qed.

  Lemma itg_s4 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x1003ac) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62500) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62500 29 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62500 29 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x1003ac) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62500) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x1003ac ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z4 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz4 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s5. exact GG1.
  Qed.

  Lemma itg_s3 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x100398) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x624a0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x624a0 40 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x624a0 40 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x100398) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x624a0) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x100398 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z3 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz3 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s4. exact GG1.
  Qed.

  Lemma itg_s2 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x100384) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62480) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62480 10 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62480 10 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x100384) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62480) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x100384 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z2 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz2 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s3. exact GG1.
  Qed.

  Lemma itg_s1 : forall (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (mk : mem), itg_G mk ->
    evt asegs itg_Q (MS (mkR (Z_to_bv 64 0x100370) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62460) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (Z_to_bv 64 ASTRCMP_STUB) fc None mk (seg_rom asegs)).
  Proof.
    intros until mk. intros GG. pose proof GG as (MU & WM & MIk & STK & ACk & CS).
    pose proof (rt_bp_base H HH) as HB. pose proof itg_geo as (G1 & G2 & G3 & G4 & G5 & G6). unfold IT_STACK, AINTRIN_STACK in *.
    destruct (itg_lit 0x62460 12 ltac:(in_lits)) as [CSTR LOW].
    destruct (cstr_icpt 0x62460 12 mk CSTR MIk ACk) as (e & BAe & FE & LE & ACe & SVe & IAe & P0e & Ne).
    destruct (itg_client mk GG) as (BAt & FT & LT & ACt & SVt).
    pose proof PRE as (_ & _ & _ & _ & IAt & L40 & QLO & _).
    eapply evt_cut.
    {
      eapply (SC (Z_to_bv 64 0x100370) (Z_to_bv 64 (SP - 16)) gp tp t0 t1 t2 (Z_to_bv 64 q) s1 (Z_to_bv 64 0x62460) (Z_to_bv 64 q) a2 a3 a4 a5 a6 a7
                 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc mk e (map bv_unsigned str) [] [] lo);
        rewrite ?u64_of_Z by lia;
        [ exact BAe | exact FE | exact BAt | exact FT
        | rewrite LE; exact ACe | rewrite LT; exact ACt | rewrite LE; exact SVe | rewrite LT; exact SVt
        | exact (proj1 (stk_split asegs mk lo (SP - 16) SP STK ltac:(lia))) | exact G6 | unfold AINTRIN_STACK; lia | exact MIk | exact ACk
        | lia | rewrite LT; lia | rewrite LE; exact IAe | rewrite LT; exact IAt
        | left; rewrite length_app, Nat2Z.inj_add, LE; cbn; clear - LOW G2; lia
        | rewrite length_app, length_map, Nat2Z.inj_add; cbn [length Z.of_nat Pos.of_succ_nat Pos.succ]; clear - QLO; lia ]. }
    intros ms1 P1. destruct P1 as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m1 & EQ1 & MU1 & WM1 & MI1 & ST1 & AC1).
    subst ms1. rewrite u64_of_Z in MU1, ST1 by lia.
    rewrite (ret_pc_even 0x100370 ltac:(lia) eq_refl).
    assert (GG1 : itg_G m1) by exact (itg_Gstep mk m1 GG MU1 WM1 MI1 ST1 AC1).
    pose proof GG1 as (_ & _ & _ & _ & _ & CS1).
    destruct (Z.eq_dec (bv_unsigned b0) 0) as [Z0|NZ].
    -
      assert (B0 : b0 = Z_to_bv 64 0) by (apply bv_eq; rewrite Z0; reflexivity). rewrite B0.
      eapply evt_of_msteps; [exact (itg_z1 gp tp u0 u1 u2 s1 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 ra s0 F fc m1 (seg_rom asegs) SP q ltac:(lia) CS1)|].
      step. apply evt_done. apply (itg_exit m1); [exact GG1 | lia].
    -
      eapply evt_of_msteps; [eapply (itg_nz1 gp tp u0 u1 u2 s1 b0 b1 b2 b3 b4 b5 b6 b7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 u3 u4 u5 u6 F fc m1 (seg_rom asegs) SP q NZ)|].
      apply itg_s2. exact GG1.
  Qed.
End ITGsites.

Section ITGmain.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Hypothesis HH : asan_rt_hyps_bp H.
  Hypothesis SC : strcmp_icpt_stmt.

  Theorem import_type_get_okA : import_type_get_stmtA.
  Proof.
    intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m str q lo
           Ha0 BA NI ACC SV IA L40 QLO ST CE LO SP16 SP47 MI AC.
    pose proof aceil_facts as ((ACF1 & ACF2) & ACF3 & ACF4).
    pose proof (bv_unsigned_in_range 64 sp) as SPR. change (bv_modulus 64) with (2 ^ 64) in SPR.
    set (SP := bv_unsigned sp) in *.
    assert (Hsp : sp = Z_to_bv 64 SP) by (subst SP; symmetry; apply Z_to_bv_bv_unsigned).
    clearbody SP. subst sp a0.
    assert (QR : 0 <= q < 2 ^ 64) by (destruct BA as (B0 & B1 & _); rewrite length_app in B1; cbn [length] in B1; lia).
    assert (PRE : itg_pre m str SP q lo).
    { split; [exact BA|]. split; [exact NI|]. split; [exact ACC|]. split; [exact SV|]. split; [exact IA|]. split; [exact L40|].
      split; [exact QLO|]. split; [exact CE|]. split; [exact LO|]. split; [exact SP47 | exact QR]. }
    unfold IT_STACK, AINTRIN_STACK in LO.
    destruct (itg_r0 ra gp tp t0 t1 t2 s0 s1 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m (seg_rom asegs) SP q lo
                ltac:(lia) QR ST ltac:(lia) MI) as (m0 & RUN0 & MU0 & WM0 & MI0 & STK0 & CS0).
    assert (GG0 : itg_G ra s0 m SP lo m0).
    { split; [eapply munch_weaken; [|exact MU0]; intros z Hz; cbn [outside] in Hz |- *; unfold IT_STACK, AINTRIN_STACK in Hz; lia|].
      split; [exact WM0|]. split; [exact MI0|]. split; [exact (STK0 _ _ ST)|]. split; [|exact CS0].
      eapply (ACONST_frame _ _ _ AC MU0 WM0). apply Forall_cons; [|apply Forall_nil].
      apply aconst_ok_high; [replace (sh AIMG_TOP) with 0x800d5000 by reflexivity; lia | right; left; lia]. }
    eapply evt_of_msteps; [exact RUN0|].
    exact (itg_s1 H HH SC ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m str SP q lo PRE t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m0 GG0).
  Qed.
End ITGmain.
