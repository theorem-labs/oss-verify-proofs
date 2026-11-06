(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_bigint.images Require Import Ubsan.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface
     L5Defs L5Core L5CoreSpecsU L5CoreKit L5OpnewU.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Lib Require Import MState Mem Cells Step Frame Exec Tac.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Bridge Require Import BrRegs BrBase BrXfer.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.CJ.Tgt Require Import F_syscalls RMallocRep.
From OSSVerify.Proofs.jsoncons.fuzz_bigint.lib Require Import L5TopKitU L5TStrSU L5TCopySU.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_bigint.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.   (* [comment removed for export] *)

Module L5TCPU.
Import L5CSU.
Section SCFG_1.
Context {SCFG_P : ScfgP}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma C1_fix : forall m A (b : byte) cs z, rw_cells rsegs m A (C1 b :: cs) -> L5.u8_at rsegs m A z -> rw_cells rsegs m A (C1 (b8 z) :: cs).
Proof.
  intros m A b cs z RW U. pose proof (TSSU.u8_of_cells _ _ _ _ RW) as U'. unfold L5.u8_at in U, U'. rewrite U in U'.
  replace (b8 z) with b; [exact RW|]. rewrite <- (definitions.Z_to_bv_bv_unsigned 8 b). unfold b8. congruence.
Qed.

Definition limb_cells (ws : list Z) : list cell := map (fun w => C8 (Z_to_bv 64 w)) ws.
Lemma limb_cells_bytes : forall ws, cells_bytes (limb_cells ws) = L5K.limb_bytes ws.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [limb_cells map cells_bytes cbytes L5K.limb_bytes flat_map]. rewrite IH. reflexivity. Qed.
Lemma limb_cells_size : forall ws, cells_size (limb_cells ws) = (8 * length ws)%nat.
Proof. induction ws as [|w ws IH]; [reflexivity|]. cbn [limb_cells map cells_size csize length]. unfold limb_cells in IH. rewrite IH. lia. Qed.
Lemma limb_cells_wf : forall ws, cells_wf (limb_cells ws).
Proof. induction ws as [|w ws IH]; [exact I|]. split; [exact I| exact IH]. Qed.

Lemma limbs_of_limb_cells : forall ws m A, Forall (fun w => 0 <= w < 2 ^ 64) ws -> rw_cells rsegs m A (limb_cells ws) -> L5.limbs_at rsegs m A ws.
Proof.
  induction ws as [|w ws IH]; intros m A RNG RW.
  - apply L5C.limbs_at_nil.
  - apply Forall_cons_iff in RNG. destruct RNG as [Rw RNG].
    change (w :: ws) with ([w] ++ ws). apply L5C.limbs_at_app.
    + intros i Hi. cbn in Hi. destruct i; [| lia]. cbn [nth]. rewrite Z.mul_0_r, Z.add_0_r.
      pose proof (TSSU.u64_of_cells _ _ _ _ RW) as U. rewrite L5.unsigned_lit in U by lia. exact U.
    + cbn [length Z.of_nat Pos.of_succ_nat]. change (limb_cells (w :: ws)) with ([C8 (Z_to_bv 64 w)] ++ limb_cells ws) in RW.
      destruct (TSSU.rw_split _ _ _ _ RW) as [_ RW2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat] in RW2.
      replace (A + 8 * 1) with (A + 8) by lia. apply IH; [exact RNG| exact RW2].
Qed.

(* [comment removed for export] *)
Lemma limbs_of_cells : forall m A ws n, Forall (fun w => 0 <= w < 2 ^ 64) ws -> n = (8 * length ws)%nat ->
  rw_cells rsegs m A [CB n (L5K.limb_bytes ws)] -> L5.limbs_at rsegs m A ws.
Proof.
  intros m A ws n RNG Hn RW. apply limbs_of_limb_cells; [exact RNG|].
  eapply TSSU.rw_recell; [exact RW| apply limb_cells_wf| |].
  - rewrite limb_cells_bytes. cbn. rewrite app_nil_r. reflexivity.
  - rewrite limb_cells_size. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma bytes_of_limbs : forall M q ws, L5.limbs_at rsegs M q ws -> 0 <= q -> q + 8 * Z.of_nat (length ws) <= 2 ^ 64 ->
  bytes_at rsegs M q (L5K.limb_bytes ws).
Proof.
  intros M q ws HL Hq Hn. apply (TKU.bytes_at_of_rdn M (8 * length ws)%nat q).
  - exact (L5K.rdn_of_limbs_at rsegs M ws q HL Hq Hn).
  - apply L5K.limb_bytes_length.
  - exact Hq.
  - lia.
Qed.

(* [comment removed for export] *)
Lemma cfb_eq : forall fbo fb' d, TCSU.cfb fbo fb' d = copy_fb fbo fb' d.
Proof. reflexivity. Qed.
Lemma cfb_range : forall fbo fb' d, 0 <= fbo < 256 -> 0 <= fb' < 256 -> 0 <= copy_fb fbo fb' d < 256.
Proof.
  intros fbo fb' d H1 H2. unfold copy_fb.
  pose proof (L5.land_byte_range fbo 252 ltac:(lia)). pose proof (L5.land_byte_range fb' 2 ltac:(lia)).
  assert (0 <= (if d then 1 else 0) < 256) by (destruct d; lia).
  apply (Bytes.lor_lt_pow2 _ _ 8); [apply (Bytes.lor_lt_pow2 _ _ 8)|]; cbn; lia.
Qed.
Lemma cfb_bit0 : forall fbo fb' d, Z.testbit (copy_fb fbo fb' d) 0 = d.
Proof.
  intros. unfold copy_fb. rewrite !Z.lor_spec, !Z.land_spec.
  change (Z.testbit 252 0) with false. change (Z.testbit 2 0) with false. rewrite !Bool.andb_false_r, Bool.orb_false_r.
  destruct d; reflexivity.
Qed.

Section S.
Variable L : heap_layout.
Variable HI : heap_iface.
Hypothesis LY : layout L.
Hypothesis HIok : heap_iface_ok L SCFG HI.

Local Ltac greg REQ k := rewrite (TKU.getr_of_eqv_lit _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ k _ REQ ltac:(lia)); cbn [nth Z.to_nat Pos.to_nat Pos.iter_op Nat.add].

Lemma defined_of_writable : forall M a n, L5.writable rsegs M a n -> 0x92000 <= a -> a + n <= 2 ^ 64 -> L5.defined M a n.
Proof.
  intros M a n W Ha Hn i Hi. specialize (W i 1%nat ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat]; lia)).
  cbn [store_ok] in W. rewrite ref_wview_overlay in W by (rewrite L5.unsigned_lit by lia; lia).
  destruct (M (Z_to_bv 64 (a + i))); [discriminate| discriminate W].
Qed.

(* [comment removed for export] *)
Lemma copy_inl : forall pc, TCSU.wci_stmt pc ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o o' sp r fbo : Z) (b' : L5.bigobj) (ws' : list Z),
    L5.bo_dyn b' = false ->
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp COPY_SCR ->
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> o' mod 8 = 0 -> sp <= o' -> o' + 32 <= hl_sptop L ->
    (o + 32 <= o' \/ o' + 32 <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        copy_post L LB cr M M' R R' o o' sp fbo b' ws' g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
Proof.
  intros pc WCI. intros until ws'. intros ND HH [Mh [Ml Mm]] HK A0 A1 RA RAOK SP TP STK U8O FBO O8 SPO OHI WO BIG LIMBS O8' SPO' OHI' SEP CONT.
  unfold cfg. change Ubsan.M.loaded_segments with rsegs in *.
  destruct STK as (SP16 & SPLO & SPHI & SPTOP & SDEF2). unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in SPLO, SDEF2.
  destruct b' as [fb' len st']. unfold L5.bo_dyn in ND. cbn [L5.bo_fb] in ND.
  destruct BIG as (YU8 & FB' & YLEN & BST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in YU8, FB', YLEN, BST.
  destruct st' as [v0 v1|cap q]. 2:{ destruct BST as [T _]. rewrite ND in T. discriminate. }
  destruct BST as (_ & Y16 & Y24 & LEN2 & V0 & V1).
  pose proof (defined_of_writable M o 32 WO ltac:(lia) ltac:(lia)) as ODEF.
  destruct (TSSU.rw_of_defined M o 32 ODEF ltac:(lia) ltac:(lia)) as [bsO OB0].
  destruct (TSSU.C1CB_of_CB M o 31 bsO OB0) as (bq & junkO & OB1). clear OB0.
  pose proof (C1_fix _ _ _ _ _ OB1 U8O) as OB. clear OB1.
  pose proof (TKU.ro_cells_u8 M o' fb' YU8 ltac:(lia) ltac:(lia)) as YB.
  pose proof (TKU.ro_cells_u64 M (o' + 8) _ YLEN ltac:(lia) ltac:(lia)) as YL.
  pose proof (TKU.ro_cells_u64 M (o' + 16) _ Y16 ltac:(lia) ltac:(lia)) as Y0.
  pose proof (TKU.ro_cells_u64 M (o' + 24) _ Y24 ltac:(lia) ltac:(lia)) as Y1.
  eapply (TKU.srz_evt_canonMS _ R _ M model K Mh Ml).
  { unfold canon_regs. rewrite RA, SP, TP, A0, A1.
    eapply WCI; [lia| lia| lia| lia| exact SEP| exact FBO| exact FB'| exact ND| exact OB| exact YB| exact YL| exact Y0| exact Y1]. }
  2:{ intros ms' PO. destruct PO as (a1' & a2' & a3' & a4' & m' & j7 & -> & _). eexists _, _, _. reflexivity. }
  intros R1c pc1 m1 R1 PO REQ1.
  destruct PO as (a1' & a2' & a3' & a4' & m' & j7 & E & OB' & MU & WM & MG). inversion E; subst R1c pc1 m1; clear E.
  rewrite (TKU.ret_pc_lit r RAOK).
  pose proof (cfb_range fbo fb' false FBO FB') as CR. rewrite <- cfb_eq in CR.
  pose proof (TSSU.rw_split m' o [C1 (b8 (TCSU.cfb fbo fb' false)); CB 7 j7] [C8 (Z_to_bv 64 (Z.of_nat len)); C8 (Z_to_bv 64 v0); C8 (Z_to_bv 64 v1)] OB') as [_ OW1].
  pose proof (TSSU.rw_split m' _ [C8 (Z_to_bv 64 (Z.of_nat len))] [C8 (Z_to_bv 64 v0); C8 (Z_to_bv 64 v1)] OW1) as [_ OW2].
  pose proof (TSSU.rw_split m' _ [C8 (Z_to_bv 64 v0)] [C8 (Z_to_bv 64 v1)] OW2) as [_ OW3]. cbn [cells_size csize Nat.add] in OW1, OW2, OW3.
  eapply (CONT fx R1 m' model Same LB cr).
  + split.
    * eapply (TKU.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R1 REQ1); try reflexivity; [exact SP| exact TP].
    * cbn [L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st]. split; [exact ND|]. split; [reflexivity|]. split; [reflexivity|]. split; [| split].
      -- (* [comment removed for export] *) unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. rewrite <- cfb_eq. split; [| split; [exact CR| split; [| split; [| split; [| split; [| split; [exact LEN2| split; [exact V0| exact V1]]]]]]]].
         ++ pose proof (TSSU.u8_of_cells _ _ _ _ OB') as U. rewrite b8_unsigned in U by lia. exact U.
         ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW1) as U. rewrite L5.unsigned_lit in U by lia. exact U.
         ++ rewrite cfb_eq. apply cfb_bit0.
         ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW2) as U. rewrite L5.unsigned_lit in U by lia. replace (o + 16) with (o + 8 + 8) by lia. exact U.
         ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW3) as U. rewrite L5.unsigned_lit in U by lia. replace (o + 24) with (o + 8 + 8 + 8) by lia. exact U.
      -- (* [comment removed for export] *) intros x OUT. apply MU. cbn. pose proof (OUT (o, 32) ltac:(left; reflexivity)) as X2. unfold L5.in_rng in X2. cbn [fst snd] in X2. lia.
      -- exact MG.
  + apply L5C.model_but_vm_refl.
  + eapply (L5C.hi_heap_client L SCFG HI LB cr M m'); [exact HIok| exact HH| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| | exact MG].
    intros a Ha. destruct (Z_le_gt_dec o a) as [Z1|Z1]; [destruct (Z_lt_le_dec a (o + 32)) as [Z2|Z2]; [right; left; lia|]|].
    all: left; apply (MU (Z_to_bv 64 a)); rewrite L5.unsigned_lit by lia; cbn; lia.
Qed.

(* [comment removed for export] *)
Lemma copy_dyn : forall pc, TCSU.wcd0_stmt pc ->
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet)
         (LB : list (Z * Z)) (cr : credit) (o o' sp r fbo : Z) (b' : L5.bigobj) (ws' : list Z),
    L5.bo_dyn b' = true -> 8 * L5.bo_cap b' <= 2 ^ 27 -> credit_ok L cr (8 * L5.bo_cap b') ->
    hi_heap HI LB cr M (m_vmmaps model) -> model_ok model -> K [] ->
    getr R 10%bv = Z_to_bv 64 o -> getr R 11%bv = Z_to_bv 64 o' ->
    getr R 1%bv = Z_to_bv 64 r -> L5.ra_ok r ->
    getr R 2%bv = Z_to_bv 64 sp -> getr R 4%bv = Z_to_bv 64 TP -> L5C.stk (hl_sptop L) M sp COPY_SCR ->
    L5.u8_at RSEGS M o fbo -> 0 <= fbo < 256 -> o mod 8 = 0 -> sp <= o -> o + 32 <= hl_sptop L -> L5.writable RSEGS M o 32 ->
    L5.big_at RSEGS M o' b' -> L5C.obj_limbs RSEGS M b' ws' -> o' mod 8 = 0 -> sp <= o' -> o' + 32 <= hl_sptop L ->
    (forall cap q, L5.bo_st b' = L5.BDyn cap q -> In (q, 8 * cap) LB) ->
    (o + 32 <= o' \/ o' + 32 <= o) ->
    (forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (g : growth) LB' cr',
        copy_post L LB cr M M' R R' o o' sp fbo b' ws' g LB' cr' ->
        model_but_vm model model' -> hi_heap HI LB' cr' M' (m_vmmaps model') ->
        srealizes RSEGS SCFG (cfg R' r M' model') K) ->
    srealizes RSEGS SCFG (cfg R pc M model) K.
Proof.
  intros pc WCD0. intros until ws'. intros DY CAP27 CRED HH [Mh [Ml Mm]] HK A0 A1 RA RAOK SP TP STK U8O FBO O8 SPO OHI WO BIG LIMBS O8' SPO' OHI' INLB SEP CONT.
  unfold cfg. change Ubsan.M.loaded_segments with rsegs in *.
  destruct STK as (SP16 & SPLO & SPHI & SPTOP & SDEF2). unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in SPLO, SDEF2.
  destruct b' as [fb' len st']. unfold L5.bo_dyn in DY. cbn [L5.bo_fb] in DY.
  destruct BIG as (YU8 & FB' & YLEN & BST). cbn [L5.bo_fb L5.bo_len L5.bo_st] in YU8, FB', YLEN, BST.
  destruct st' as [v0 v1|cap q]. { destruct BST as [T _]. rewrite DY in T. discriminate. }
  cbn [L5.bo_cap L5.bo_st] in CAP27, CRED.
  destruct BST as (_ & Y16 & Y24 & LENC & CAPR & Q8 & QLO & QHI).
  pose proof (INLB cap q eq_refl) as INQ. clear INLB.
  destruct LIMBS as (WLEN & WRNG & WL). cbn [L5.bo_len L5.bo_st] in WLEN, WL.
  pose proof (hio_wf L SCFG HI HIok _ _ _ _ HH) as (WFB & _).
  destruct (WFB _ INQ) as ((QB1lo & QB1 & QB2 & QB3 & QB4) & _). cbn [fst snd] in QB1lo. cbn [fst snd] in QB1, QB4. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in QB1.
  (* [comment removed for export] *)
  pose proof (defined_of_writable M o 32 WO ltac:(lia) ltac:(lia)) as ODEF.
  destruct (TSSU.rw_of_defined M o 32 ODEF ltac:(lia) ltac:(lia)) as [bsO OB0].
  destruct (TSSU.C1CB_of_CB M o 31 bsO OB0) as (bq & junkO & OB1). clear OB0.
  pose proof (C1_fix _ _ _ _ _ OB1 U8O) as OB. clear OB1.
  pose proof (TKU.ro_cells_u8 M o' fb' YU8 ltac:(lia) ltac:(lia)) as YB.
  pose proof (TKU.ro_cells_u64 M (o' + 8) _ YLEN ltac:(lia) ltac:(lia)) as YL.
  pose proof (TKU.ro_cells_u64 M (o' + 16) _ Y16 ltac:(lia) ltac:(lia)) as Y0.
  pose proof (TKU.ro_cells_u64 M (o' + 24) _ Y24 ltac:(lia) ltac:(lia)) as Y1.
  assert (ST0 : stk rsegs M (sp - 8304) sp).
  { apply TKU.stk_of_defined; [| lia| lia| lia]. replace (sp - (sp - 8304)) with 8304 by lia. exact SDEF2. }
  (* [comment removed for export] *)
  eapply (TKU.srz_evt_canonMS _ R _ M model K Mh Ml).
  { unfold canon_regs. rewrite RA, SP, TP, A0, A1.
    eapply (TCSU.wcd01 pc WCD0 _ (Z_to_bv 64 sp)) with (cap := cap) (q := q); rewrite ?L5.unsigned_lit by lia;
      [exact ST0| lia| lia| lia| lia| lia| lia| exact SEP| lia| exact FBO| exact FB'| exact DY| lia| lia| exact OB| exact YB| exact YL| exact Y0| exact Y1]. }
  2:{ intros ms' (a1' & a2' & a3' & m' & junk & j7 & -> & _). eexists _, _, _. reflexivity. }
  intros R1c pc1 m1' R1 (a1' & a2' & a3' & m1 & junk & j7 & E & FR1 & OB1 & MU1 & WM1 & MG1 & ST1) REQ1. inversion E; subst R1c pc1 m1'; clear E.
  rewrite ?L5.unsigned_lit in FR1, MU1, ST1 by lia.
  assert (OUT1 : forall a, 0 <= a < 2 ^ 64 -> ~ (sp - 64 <= a < sp) -> ~ (o <= a < o + 32) -> m1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
  { intros a Ha Hn Hn'. apply MU1. cbn. rewrite L5.unsigned_lit by lia. lia. }
  assert (HH1 : hi_heap HI LB cr m1 (m_vmmaps model)).
  { eapply (L5C.hi_heap_client L SCFG HI LB cr M m1); [exact HIok| exact HH| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| | exact MG1].
    intros a Ha. destruct (Z_le_gt_dec (sp - 64) a) as [X|X]; [destruct (Z_lt_le_dec a sp) as [Y|Y]; [right; left; lia|]|].
    all: destruct (Z_le_gt_dec o a) as [Z1|Z1]; [destruct (Z_lt_le_dec a (o + 32)) as [Z2|Z2]; [right; left; lia|]|].
    all: left; apply OUT1; lia. }
  (* [comment removed for export] *)
  eapply (L5NEWU.opnew_ok L HI LY HIok fx R1 m1 model K LB cr (8 * cap) (sp + -64) 0x2239c).
  - exact HH1.
  - split; [exact Mh| split; [exact Ml| exact Mm]].
  - exact HK.
  - greg REQ1 10. f_equal. lia.
  - lia.
  - exact CRED.
  - greg REQ1 1. reflexivity.
  - split; [lia| reflexivity].
  - greg REQ1 2. unfold wz. rewrite L5.unsigned_lit by lia. reflexivity.
  - greg REQ1 4. reflexivity.
  - split; [clear -SP16; Z.div_mod_to_equations; lia|]. split; [unfold OPNEW_SCR, HEAP_STACK; lia|]. split; [lia|]. split; [lia|].
    unfold OPNEW_SCR, HEAP_STACK. intros i Hi. apply MG1. replace (sp + -64 - (16 + 8224) + i) with (sp - (64 + (16 + 8224)) + i) by lia. apply SDEF2. lia.
  - (* [comment removed for export] *)
    intros fx2 R2 M2 model2 A RA2 RP12 FRESH HP12 MBV12 HH2. unfold L5CSU.cfg.
    pose proof (L5C.halted_but_vm _ _ MBV12) as Mh2. rewrite Mh in Mh2.
    pose proof (L5C.lazy_but_vm _ _ MBV12) as Ml2. rewrite Ml in Ml2.
    pose proof FRESH as [[B1lo [B1 [B2 [B3 B4]]]] [APART BDEF]]. rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in B1.
    destruct HP12 as (KEPT12 & SDEF12 & CDEF12). unfold OPNEW_SCR, HEAP_STACK in SDEF12, CDEF12.
    pose proof (APART _ INQ) as APQ. cbn [fst snd] in APQ.
    assert (KS : forall a, sp - 64 <= a < 2 ^ 47 -> M2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)).
    { intros a Ha. apply KEPT12. apply (L5C.kept_stack L); [unfold OPNEW_SCR, HEAP_STACK; lia| unfold OPNEW_SCR, HEAP_STACK; lia| lia| rewrite (ly_errno L LY); lia| lia| intros r0 []]. }
    assert (KQ : forall a, q <= a < q + 8 * cap -> M2 (Z_to_bv 64 a) = M (Z_to_bv 64 a)).
    { intros a Ha. rewrite <- (OUT1 a) by lia. apply KEPT12.
      apply (L5C.kept_block L LB (sp + -64) OPNEW_SCR [] q (8 * cap)); [exact INQ| lia| lia| lia| rewrite (ly_errno L LY); lia| intros r0 []]. }
    assert (FR2 : rw_cells rsegs M2 (sp + -64) [CB 32 junk; C8 (getr R 18%bv); C8 (getr R 9%bv); C8 (getr R 8%bv); C8 (Z_to_bv 64 r)]).
    { eapply TKU.rw_cells_agree; [exact FR1| |]; cbn [cells_size csize Nat.add]; intros a Ha; unfold wa; [apply KS; lia|].
      rewrite KS by lia. apply (TSSU.rw_cells_defined _ _ _ a FR1); cbn [cells_size csize Nat.add]; lia. }
    assert (OB2 : rw_cells rsegs M2 o [C1 (b8 (TCSU.cfb fbo fb' true)); CB 7 j7; C8 (Z_to_bv 64 (Z.of_nat len)); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 0)]).
    { eapply TKU.rw_cells_agree; [exact OB1| |]; cbn [cells_size csize Nat.add]; intros a Ha; unfold wa; [apply KS; lia|].
      rewrite KS by lia. apply (TSSU.rw_cells_defined _ _ _ a OB1); cbn [cells_size csize Nat.add]; lia. }
    assert (YQ2 : ro_cells rsegs M2 (o' + 24) [C8 (Z_to_bv 64 q)]).
    { eapply TKU.ro_cells_agree; [exact Y1|]. cbn [cells_size csize Nat.add]. intros a Ha. unfold wa. rewrite KS by lia. apply OUT1; lia. }
    assert (PDEF : forall i, 0 <= i < Z.of_nat (8 + Z.to_nat (cap * 8 - 8)) -> M2 (Z_to_bv 64 (A + i)) <> None) by (intros i Hi; apply BDEF; lia).
    destruct (TSSU.rw_of_defined M2 A _ PDEF ltac:(lia) ltac:(lia)) as [bsP PB0].
    pose proof (TCSU.CB_cut1 M2 A 8 _ bsP PB0) as PB2. clear PB0.
    assert (WL2 : L5.limbs_at rsegs M2 q ws').
    { eapply (L5C.limbs_at_agree rsegs M M2); [| lia| lia| exact WL]. intros a Ha. apply KQ. lia. }
    pose proof (bytes_of_limbs M2 q ws' WL2 ltac:(lia) ltac:(lia)) as SB2.
    (* [comment removed for export] *)
    eapply (TKU.srz_evt_canonMS _ R2 _ M2 model2 K Mh2 Ml2).
    { rewrite (TKU.canon_after _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R1 R2 REQ1 RP12). rewrite RA2.
      eapply (TCSU.wcd2 _ (Z_to_bv 64 sp)) with (o := o) (o' := o') (A := A) (cap := cap) (len := Z.of_nat len) (q := q) (sbytes := L5K.limb_bytes ws');
        rewrite ?L5.unsigned_lit by lia;
        [lia| lia| lia| lia| lia| lia| lia| lia| lia| lia| lia| lia| lia| exact SEP| clear -B2; Z.div_mod_to_equations; lia| exact Q8| rewrite L5K.limb_bytes_length; lia| exact FR2| exact OB2| exact YQ2| exact PB2| exact SB2]. }
    2:{ intros ms' PO. destruct PO as (t0' & t1' & t2' & a1'' & a2'' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & J2 & -> & _). eexists _, _, _. reflexivity. }
    intros R3c pc3 m3' R3 PO REQ3.
    destruct PO as (t0' & t1' & t2' & a1'' & a2'' & a3'' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m3 & J2 & E & OB3 & DST3 & BT3 & SB3 & FR3 & MU3 & WM3 & MG3).
    inversion E; subst R3c pc3 m3'; clear E. rewrite ?L5.unsigned_lit in FR3 by lia.
    rewrite (TKU.ret_pc_lit r RAOK).
    pose proof (cfb_range fbo fb' true FBO FB') as CR. rewrite <- cfb_eq in CR.
    pose proof (TSSU.rw_split m3 o [C1 (b8 (TCSU.cfb fbo fb' true)); CB 7 j7] [C8 (Z_to_bv 64 (Z.of_nat len)); C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 A)] OB3) as [_ OW1].
    pose proof (TSSU.rw_split m3 _ [C8 (Z_to_bv 64 (Z.of_nat len))] [C8 (Z_to_bv 64 cap); C8 (Z_to_bv 64 A)] OW1) as [_ OW2].
    pose proof (TSSU.rw_split m3 _ [C8 (Z_to_bv 64 cap)] [C8 (Z_to_bv 64 A)] OW2) as [_ OW3]. cbn [cells_size csize Nat.add] in OW1, OW2, OW3.
    assert (BDEF3 : L5.defined m3 A (8 * cap)).
    { intros i Hi. destruct (Z_lt_le_dec (A + i) (A + Z.of_nat len * 8)).
      - apply (TSSU.rw_cells_defined _ _ _ (A + i) DST3); cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia.
      - apply (TSSU.rw_cells_defined _ _ _ (A + i) BT3); cbn [cells_size csize Nat.add]; rewrite ?Z2Nat.id by lia; lia. }
    eapply (CONT fx2 R3 m3 model2 (Grown A cap) ((A, 8 * cap) :: LB) (debit L cr (8 * cap))).
    + split.
      * eapply (TKU.regs_preserved_intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ R R3 REQ3); try reflexivity; [exact SP| exact TP].
      * cbn [L5.bo_dyn L5.bo_fb L5.bo_len L5.bo_st L5.bo_cap]. split; [exact DY|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [| split; [| split]].
        -- (* [comment removed for export] *) split; [exact (proj1 FRESH)|]. split; [exact APART| exact BDEF3].
        -- (* [comment removed for export] *) unfold L5.big_at. cbn [L5.bo_fb L5.bo_len L5.bo_st]. rewrite <- cfb_eq.
           split; [| split; [exact CR| split; [| split; [| split; [| split; [| split; [exact LENC| split; [exact CAPR| split; [clear -B2; Z.div_mod_to_equations; lia| split; [lia| split; [lia| apply TKU.hull_apart_of; exact B1]]]]]]]]]]].
           ++ pose proof (TSSU.u8_of_cells _ _ _ _ OB3) as U. rewrite b8_unsigned in U by lia. exact U.
           ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW1) as U. rewrite L5.unsigned_lit in U by lia. exact U.
           ++ rewrite cfb_eq. apply cfb_bit0.
           ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW2) as U. rewrite L5.unsigned_lit in U by lia. replace (o + 16) with (o + 8 + 8) by lia. exact U.
           ++ pose proof (TSSU.u64_of_cells _ _ _ _ OW3) as U. rewrite L5.unsigned_lit in U by lia. replace (o + 24) with (o + 8 + 8 + 8) by lia. exact U.
        -- (* [comment removed for export] *) split; [exact WLEN|]. split; [exact WRNG|]. cbn [L5.bo_st].
           apply (limbs_of_cells m3 A ws' (Z.to_nat (Z.of_nat len * 8)) WRNG ltac:(rewrite <- WLEN; lia) DST3).
        -- (* [comment removed for export] *) split; [| split].
           ++ intros a (Ha & CA & NE & OW). unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in CA.
              assert (NO : ~ (o <= a < o + 32)). { intros X. apply (OW (o, 32)); [left; reflexivity| unfold L5.in_rng; cbn; lia]. }
              assert (NS : ~ (sp - 8304 <= a < sp)).
              { destruct CA as [(b & Hb & Hr)|[[C1' C2]|[C1' C2]]]; [| lia| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in C1'; lia].
                destruct (WFB b Hb) as ((D1lo & D1 & D2 & D3 & D4) & _). cbn [fst snd] in D1lo. lia. }
              assert (NB : ~ (A <= a < A + 8 * cap)).
              { destruct CA as [(b & Hb & Hr)|[[C1' C2]|[C1' C2]]]; [| lia| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY) in C1'; lia].
                pose proof (APART b Hb). lia. }
              rewrite (MU3 (Z_to_bv 64 a)) by (rewrite L5.unsigned_lit by lia; cbn; lia).
              rewrite KEPT12. { apply OUT1; lia. }
              split; [exact Ha|]. split; [| split; [exact NE| intros r0 []]].
              destruct CA as [IB|[[C1' C2]|IM]]; [left; exact IB| right; left; split; [exact C1'| unfold OPNEW_SCR, HEAP_STACK; lia]| right; right; exact IM].
           ++ unfold COPY_SCR, OPNEW_SCR, HEAP_STACK. intros i Hi. destruct (Z_lt_le_dec (sp - (64 + (16 + 8224)) + i) (sp - 64)).
              ** rewrite (MU3 (Z_to_bv 64 _)) by (rewrite L5.unsigned_lit by lia; cbn; lia).
                 replace (sp - (64 + (16 + 8224)) + i) with (sp + -64 - (16 + 8224) + (i)) by lia. apply SDEF12. lia.
              ** apply (TSSU.rw_cells_defined _ _ _ _ FR3); cbn [cells_size csize Nat.add]; lia.
           ++ intros a Ha CA NE D0. apply MG3. apply CDEF12; [exact Ha| | exact NE| apply MG1; exact D0].
              unfold COPY_SCR, OPNEW_SCR, HEAP_STACK in CA.
              destruct CA as [IB|[[C1' C2]|IM]]; [left; exact IB| right; left; split; [exact C1'| unfold OPNEW_SCR, HEAP_STACK; lia]| right; right; exact IM].
    + exact MBV12.
    + eapply (L5C.hi_heap_client L SCFG HI _ _ M2 m3); [exact HIok| exact HH2| exact (ly_ro L LY)| rewrite ?(ly_img_lo L LY), ?(ly_img_hi L LY); lia| lia| | exact MG3].
      intros a Ha. destruct (Z_le_gt_dec o a) as [X|X]; [destruct (Z_lt_le_dec a (o + 32)) as [Y|Y]; [right; left; lia|]|].
      all: destruct (Z_le_gt_dec A a) as [Z1|Z1]; [destruct (Z_lt_le_dec a (A + 8 * cap)) as [Z2|Z2]; [right; right; exists (A, 8 * cap); split; [left; reflexivity| cbn; lia]|]|].
      all: left; apply (MU3 (Z_to_bv 64 a)); rewrite L5.unsigned_lit by lia; cbn; lia.
Qed.

(* [comment removed for export] *)
Theorem copy_ok_at : forall pc, TCSU.wci_stmt pc -> TCSU.wcd0_stmt pc -> copy_spec_at pc L HI.
Proof.
  intros pc WCI WCD0 fx R M model K LB cr o o' sp r fbo b' ws' HH MOK HK A0 A1 DYN RA RAOK SP TP STK U8O FBO O8 SPO OHI WO BIG LIMBS O8' SPO' OHI' INLB SEP CONT.
  destruct (L5.bo_dyn b') eqn:DY.
  - destruct (DYN eq_refl) as [C1 C2]. eapply (copy_dyn pc WCD0); eauto.
  - eapply (copy_inl pc WCI); eauto.
Qed.
Theorem copy_ok : copy_spec L HI.
Proof. exact (copy_ok_at _ TCSU.wci TCSU.wcd0). Qed.
Theorem copya_ok : copya_spec L HI.
Proof. exact (copy_ok_at _ TCSU.wcia TCSU.wcd0a). Qed.

End S.
End SCFG_1.

End L5TCPU.
