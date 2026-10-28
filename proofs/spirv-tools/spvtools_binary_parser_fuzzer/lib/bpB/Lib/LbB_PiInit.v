(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep BsStack0 RtB_Iface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface FPSteps SymExec3.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require RtB_Td.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HStmts.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require HLib.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibCont Require Import CRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibPrs Require Import PrsInv PmBase.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB LbB_PrsStmt LbB_FKit LbB_Own LbB_PmBase LbB_PiStmt.
Import ListNotations.
Open Scope Z_scope.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.

Definition pi_c0 (st : stateC) : pmc :=
  {| c_widx := st_widx st; c_icount := st_icount st; c_endian := st_endian st; c_reqconv := st_flags st;
     c_m1 := st_m1 st; c_m2 := st_m2 st; c_m3 := st_m3 st;
     c_v1 := (t3a (st_v1 st), 0, 25); c_v2 := (t3a (st_v2 st), [], 25); c_v3 := (t3a (st_v3 st), [], 25);
     c_tr := [] |}.

Definition pi_hdr (st : stateC) (words n e : Z) : Prop :=
  st_words st = words /\ st_nwords st = n /\ st_widx st = 5 /\ st_icount st = 0 /\
  st_endian st = e /\ st_flags st = e /\ (e = 0 \/ e = 1) /\
  st_m1 st = (0, 0, []) /\ st_m2 st = (0, 0, []) /\ st_m3 st = (0, 0, []) /\
  t3a (st_v1 st) = t3b (st_v1 st) /\ t3a (st_v2 st) = t3b (st_v2 st) /\ t3a (st_v3 st) = t3b (st_v3 st) /\
  t3a (st_v1 st) <> 0 /\ t3a (st_v2 st) <> 0 /\ t3a (st_v3 st) <> 0 /\
  t3c (st_v1 st) = t3a (st_v1 st) + 500 /\ t3c (st_v2 st) = t3a (st_v2 st) + 100 /\ t3c (st_v3 st) = t3a (st_v3 st) + 100.

Lemma pi_blocks : forall st words n e, pi_hdr st words n e ->
  state_blocks st = [(t3a (st_v1 st), 500); (t3a (st_v2 st), 100); (t3a (st_v3 st), 100)]
  /\ c_blocks (pi_c0 st) = [(t3a (st_v1 st), 500); (t3a (st_v2 st), 100); (t3a (st_v3 st), 100)].
Proof.
  intros [w0 n0 d0 wi ic en fl m1 m2 m3 [[b1 e1] c1] [[b2 e2] c2] [[b3 e3] c3]] words n e
         (_ & _ & _ & _ & _ & _ & _ & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
  cbn [st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 t3a t3b t3c fst snd] in *. subst m1 m2 m3 c1 c2 c3.
  unfold state_blocks, c_blocks, vec_blocks, vec_opnd_blocks, pi_c0, umap_blocks.
  cbn [c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr st_m1 st_m2 st_m3 st_v1 st_v2 st_v3 t3a t3b t3c fst snd Z.eqb map app].
  destruct (Z.eqb_spec b1 0); [contradiction|]. destruct (Z.eqb_spec b2 0); [contradiction|]. destruct (Z.eqb_spec b3 0); [contradiction|].
  unfold OPND_SZ. cbn [app]. split; repeat f_equal; lia.
Qed.

Lemma fold_perm : forall (f : Z * Z -> Z) l l', Permutation l l' ->
  fold_right (fun x acc => f x + acc) 0 l = fold_right (fun x acc => f x + acc) 0 l'.
Proof. intros f l l' P. induction P; cbn [fold_right]; lia. Qed.

Lemma lb_small_lbl : forall LB, lb_small LB = fold_right (fun x acc => nsmall (snd x) + acc) 0 (lbl LB).
Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbl in *. cbn [map fold_right]. rewrite lb_small_cons, IH. reflexivity. Qed.
Lemma nlarge_lbl : forall LB, nlarge LB = fold_right (fun x acc => nlg (snd x) + acc) 0 (lbl LB).
Proof. induction LB as [|b LB IH]; [reflexivity|]. unfold lbl in *. cbn [map fold_right]. rewrite nlarge_cons, IH. reflexivity. Qed.
Lemma length_lbl : forall LB, length (lbl LB) = length LB.
Proof. intros LB. unfold lbl. apply length_map. Qed.

Lemma pi_meas : forall (LBs : list block) st words n e, pi_hdr st words n e -> Permutation (lbl LBs) (state_blocks st) -> 0 <= n ->
  pm_meas_ok n LBs.
Proof.
  intros LBs st words n e FR P Hn. destruct (pi_blocks st words n e FR) as [E _]. rewrite E in P.
  unfold pm_meas_ok. rewrite lb_small_lbl, nlarge_lbl, <- length_lbl.
  rewrite (fold_perm _ _ _ P), (fold_perm (fun x => nlg (snd x)) _ _ P), (Permutation_length P).
  cbn [fold_right snd length]. unfold nsmall, nlg, po_small, po_cnt, po_large. cbn -[Z.div].
  assert (0 <= n / 2) by (apply Z.div_pos; lia). assert (0 <= n / 3) by (apply Z.div_pos; lia). lia.
Qed.

Lemma rdn_2_split : forall segs m (x : word) b0 b1, PropExec.rdn segs m x 2 = Some [b0; b1] ->
  PropExec.rdn segs m x 1 = Some [b0] /\ PropExec.rdn segs m (x + 1)%bv 1 = Some [b1].
Proof.
  intros segs m x b0 b1 R. cbn [PropExec.rdn] in *.
  destruct (match m x with Some b => Some b | None => PropExec.seg_rom segs x end) as [c0|]; [|discriminate].
  destruct (match m (x + 1)%bv with Some b => Some b | None => PropExec.seg_rom segs (x + 1)%bv end) as [c1|]; [|discriminate].
  injection R as -> ->. split; reflexivity.
Qed.

Lemma fld2_split01 : forall m a e, 0 <= a -> a + 2 < 2 ^ 64 -> (e = 0 \/ e = 1) ->
  fld ASEGS m a 2 e -> fld ASEGS m a 1 e /\ fld ASEGS m (a + 1) 1 0.
Proof.
  intros m a e H0 H1 He F. unfold fld in *.
  assert (W : word_to_le_bytes 2 (Z_to_bv 64 e) = [Z_to_bv 8 e; Z_to_bv 8 0] /\ word_to_le_bytes 1 (Z_to_bv 64 e) = [Z_to_bv 8 e])
    by (destruct He as [-> | ->]; split; reflexivity).
  destruct W as [W2 W1]. rewrite W2 in F. rewrite W1.
  change (word_to_le_bytes 1 (Z_to_bv 64 0)) with [Z_to_bv 8 0].
  destruct (rdn_2_split ASEGS m _ _ _ F) as [F1 F2]. split; [exact F1|].
  replace (Z_to_bv 64 (a + 1)) with (Z_to_bv 64 a + 1)%bv; [exact F2|].
  apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_unsigned (1%bv : bv 64)) with 1.
  rewrite (Z.mod_small a) by lia. rewrite (Z.mod_small (a + 1)) by lia. reflexivity.
Qed.

Lemma lbl_blk : forall LB A n, In (A, n) (lbl LB) -> exists pid, In (pid, A, n) LB.
Proof.
  intros LB A n Hin. unfold lbl in Hin. apply in_map_iff in Hin. destruct Hin as ([[pid A'] n'] & E & Hin). cbn in E.
  injection E as -> ->. exists pid. exact Hin.
Qed.

Section PiSh.
  Context {HCEIL : HeapCeil}.

  Lemma addr_cc_disj : forall m A n B k o l, addressable m A n -> SHAD m B (cc_gen k 0) -> 0 < k -> 0 < l ->
    0 <= o -> o + l <= n -> n mod 8 = 0 -> o mod 8 = 0 -> A + o + l <= B \/ B + k <= A + o.
  Proof.
    intros m A n B k o l AD SB Hk Hl Ho Hon Hn8 Ho8.
    destruct (Z_le_gt_dec (A + o + l) B) as [L|L]; [left; exact L|].
    destruct (Z_le_gt_dec (B + k) (A + o)) as [R|R]; [right; exact R|].
    exfalso.
    pose proof AD as [Hn0 (A0 & A8 & _)]. pose proof SB as (B0 & B8 & _).
    assert (G8 : Z.max (A + o) B mod 8 = 0).
    { destruct (Z.max_spec (A + o) B) as [[_ ->]|[_ ->]]; [exact B8|].
      rewrite Z.add_mod, A8, Ho8 by lia. reflexivity. }
    assert (G1 : A + o <= Z.max (A + o) B /\ B <= Z.max (A + o) B /\ Z.max (A + o) B < A + o + l /\ Z.max (A + o) B < B + k)
      by lia.
    set (g := Z.max (A + o) B) in *. clearbody g.
    assert (Q1 : 8 * ((g - A) / 8) + 8 <= n) by (Z.div_mod_to_equations; lia).
    pose proof (addressable_read0 m A n g _ AD ltac:(lia) Q1 eq_refl) as R1.
    assert (NTH : nth_error (cc_gen k 0) (Z.to_nat ((g - B) / 8)) = Some (b8 0xfc)).
    { unfold cc_gen, poison_bytes. change (shadow_of 0) with (@nil byte). cbn [app].
      apply nth_error_repeat. unfold nsh.
      assert (IX : 0 <= (g - B) / 8 < (k + 7) / 8 - (0 + 7) / 8) by (Z.div_mod_to_equations; lia).
      lia. }
    pose proof (SHAD_read_at m B (cc_gen k 0) g (b8 0xfc) _ SB ltac:(lia) NTH eq_refl) as R2.
    rewrite R1 in R2. injection R2 as E. vm_compute in E. discriminate.
  Qed.
End PiSh.

Section PiInit.
  Context {HCEIL : HeapCeil}.
  Variable H : asr.
  Variable LINV : mem -> Prop.

  Lemma pi_vec_opnd : forall s LB m v b, RHEAP_block_range H -> as_RHEAP H s LB m ->
    @vraw AC_A ASEGS LY_A MI_A (lbl LB) m v b b (b + 500) -> b <> 0 -> mdef m v 24 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    (v + 24 <= b \/ b + 500 <= v) ->
    @vec_opnd AC_A ASEGS LY_A MI_A (lbl LB) m v b 0 25.
  Proof.
    intros s LB m v b HBR RH [Vb Ve Vc Vblk] Hb HD Hv Hv' Hdj.
    destruct Vblk as [(E & _)|(_ & HIn & _)]; [contradiction|].
    replace (b + 500 - b) with (OPND_SZ * 25) in HIn by (unfold OPND_SZ; lia).
    destruct (lbl_blk LB _ _ HIn) as (pid & Hin).
    pose proof (HBR _ _ _ _ RH Hin) as (B0 & B16 & Bn & BT & Bc & BF & BA). cbn [blk_addr blk_size fst snd] in *.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold vec_opnd. unfold OPND_SZ in *.
    split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [lia|].
    split; [right; repeat split; try lia; exact HIn|].
    split; [exact (proj2 Vb)|]. split; [replace (b + 20 * 0) with b by lia; exact (proj2 Ve)|].
    replace (b + 20 * 25) with (b + 500) by lia. exact (proj2 Vc).
  Qed.

  Lemma pi_vec32 : forall s LB m v b, RHEAP_block_range H -> as_RHEAP H s LB m ->
    @vraw AC_A ASEGS LY_A MI_A (lbl LB) m v b b (b + 100) -> b <> 0 -> mdef m v 24 -> 0 <= v -> v + 24 <= 2 ^ 63 ->
    (v + 24 <= b \/ b + 100 <= v) ->
    @vec32 AC_A ASEGS LY_A MI_A (lbl LB) m v b [] 25.
  Proof.
    intros s LB m v b HBR RH [Vb Ve Vc Vblk] Hb HD Hv Hv' Hdj.
    destruct Vblk as [(E & _)|(_ & HIn & _)]; [contradiction|].
    replace (b + 100 - b) with (4 * 25) in HIn by lia.
    destruct (lbl_blk LB _ _ HIn) as (pid & Hin).
    pose proof (HBR _ _ _ _ RH Hin) as (B0 & B16 & Bn & BT & Bc & BF & BA). cbn [blk_addr blk_size fst snd] in *.
    pose proof aceil_facts as ((AC1 & AC2) & AC3 & AC4).
    unfold vec32. unfold Zlen. cbn [length Z.of_nat].
    split; [exact Hv|]. split; [exact Hv'|]. split; [exact HD|]. split; [lia|].
    split; [right; repeat split; try lia; exact HIn|].
    split; [exact (proj2 Vb)|]. split; [replace (b + 4 * Z.of_nat 0) with b by lia; exact (proj2 Ve)|].
    split; [replace (b + 4 * 25) with (b + 100) by lia; exact (proj2 Vc)|].
    intros i Hi. lia.
  Qed.

  Local Ltac pic := cbn [pi_c0 c_widx c_icount c_endian c_reqconv c_m1 c_m2 c_m3 c_v1 c_v2 c_v3 c_tr
                         st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3
                         t3a t3b t3c fst snd].

  Lemma pi_init : forall (w : piw H) (s : as_St H) (LB LBs : list block) (LF : list fframe) (m : mem) (c : parserC) (e : Z),
    piw_ok H w LF m ->
    parser_repA LB m (pw_p H w) c -> parser_sh m (pw_p H w) c ->
    pc_cons c = pw_cons H w -> pc_user c = pw_user H w -> st_diag (pc_state c) = pw_diag H w ->
    pi_hdr (pc_state c) (pw_words H w) (pw_n H w) e ->
    state_own LB (pw_LB0 H w) LBs (pc_state c) -> lb_own LBs m ->
    as_RHEAP H s LB m -> mem_inv asegs m -> (exists errv : word, rw_cells asegs m (errno_addr (Z_to_bv 64 ATP)) [C4 errv]) ->
    as_rauxv_ok H m (pw_B H w) -> ACONST m -> stack0 m (pw_lo H w) (pw_shi H w) -> LINV m ->
    wr_at asegs m (pw_cons H w) 48 ->
    pw_words H w <> 0 -> 5 <= pw_n H w ->
    as_AL H s >= as_AL H (pw_s0 H w) - pm_phi (pi_c0 (pc_state c)) ->
    pm_cap (pi_c0 (pc_state c)) + PM_RESERVE <= po_cost (pw_n H w) -> po_cost (pw_n H w) <= as_AL H (pw_s0 H w) ->
    RHEAP_block_range H ->
    PIX H LINV w s LB LBs m (pi_c0 (pc_state c)).
  Proof.
    intros w s LB LBs LF m c e OK PR PSH HC HU HD HDR SOWN LBOWN RH MI ERR RAUX AC S0 LI CWR HW HN AL1 AL2 AL3 HBR.
    pose proof (pi_blocks _ _ _ _ HDR) as [SB CB].
    pose proof (pi_meas LBs (pc_state c) _ _ _ HDR (proj2 SOWN) ltac:(lia)) as MEAS.
    pose proof OK as [_ _ _ _ _ _ _ _ WOK _ _ _].
    destruct WOK as (pw' & k & _ & _ & _ & _ & _ & WMD & _).
    destruct PSH as (PA & CA & SSH).
    destruct PR as [PRcons PRuser PRhdr PRins PRhunk PRst PRdef PRal PRrange PRconsf PRconsm PRconsd].
    destruct c as [cons user st]. cbn [pc_cons pc_user pc_state] in *. subst cons user.
    destruct PRst as [W0 W1 W2 W3 W4 W5 W6 M1 M2 M3 V1 V2 V3 SD SAL SND].
    destruct SSH as (U1 & U2 & U3 & VS1 & VS2 & VS3).
    destruct st as [words0 n0 d0 wi ic en fl m1 m2 m3 [[b1 e1] c1] [[b2 e2] c2] [[b3 e3] c3]].
    destruct HDR as (Hw & Hn & Hwi & Hic & Hen & Hfl & He & Hm1 & Hm2 & Hm3 & E1 & E2 & E3 & N1 & N2 & N3 & C1 & C2 & C3).
    pic. cbn [st_words st_nwords st_diag st_widx st_icount st_endian st_flags st_m1 st_m2 st_m3 st_v1 st_v2 st_v3
              t3a t3b t3c fst snd] in *.
    subst words0 n0 d0 wi ic en fl m1 m2 m3 e1 e2 e3 c1 c2 c3.
    destruct PRrange as (P0 & P47). unfold PARSER_SIZE in P47.
    set (p := pw_p H w) in *.
    replace (p + ST_OFF) with (p + O_WORDS) in W0 by (unfold ST_OFF, O_WORDS; lia).
    replace (p + ST_OFF + 8) with (p + O_N) in W1 by (unfold ST_OFF, O_N; lia).
    replace (p + ST_OFF + 16) with (p + O_DIAG) in W2 by (unfold ST_OFF, O_DIAG; lia).
    replace (p + ST_OFF + 24) with (p + O_WIDX) in W3 by (unfold ST_OFF, O_WIDX; lia).
    replace (p + ST_OFF + 32) with (p + O_ICOUNT) in W4 by (unfold ST_OFF, O_ICOUNT; lia).
    replace (p + ST_OFF + 40) with (p + O_ENDIAN) in W5 by (unfold ST_OFF, O_ENDIAN; lia).
    replace (p + ST_OFF + 44) with (p + O_FLAGS) in W6 by (unfold ST_OFF, O_FLAGS; lia).
    replace (p + ST_OFF + 48) with (p + O_M1) in M1 by (unfold ST_OFF, O_M1; lia).
    replace (p + ST_OFF + 88) with (p + O_M2) in M2 by (unfold ST_OFF, O_M2; lia).
    replace (p + ST_OFF + 128) with (p + O_M3) in M3 by (unfold ST_OFF, O_M3; lia).
    replace (p + ST_OFF + 168) with (p + O_V1) in V1 by (unfold ST_OFF, O_V1; lia).
    replace (p + ST_OFF + 192) with (p + O_V2) in V2 by (unfold ST_OFF, O_V2; lia).
    replace (p + ST_OFF + 216) with (p + O_V3) in V3 by (unfold ST_OFF, O_V3; lia).
    assert (VD : forall o, 168 <= o -> o + 24 <= 240 -> mdef m (p + ST_OFF + o) 24).
    { intros o Ho1 Ho2 i Hi. replace (p + ST_OFF + o + i) with (p + ST_OFF + (o + i)) by lia. apply SD. lia. }
    pose proof (VD 168 ltac:(lia) ltac:(lia)) as VD1. pose proof (VD 192 ltac:(lia) ltac:(lia)) as VD2.
    pose proof (VD 216 ltac:(lia) ltac:(lia)) as VD3.
    replace (p + ST_OFF + 168) with (p + O_V1) in VD1 by (unfold ST_OFF, O_V1; lia).
    replace (p + ST_OFF + 192) with (p + O_V2) in VD2 by (unfold ST_OFF, O_V2; lia).
    replace (p + ST_OFF + 216) with (p + O_V3) in VD3 by (unfold ST_OFF, O_V3; lia).
    pose proof (fld2_split01 m (p + O_FLAGS) e ltac:(unfold O_FLAGS; lia) ltac:(unfold O_FLAGS; lia) He (proj2 W6)) as [FL1 FL2].
    assert (SH1 : SHAD m b1 (cc_gen 500 0)).
    { specialize (VS1 N1). cbn [t3a t3b t3c fst snd] in VS1.
      replace (b1 + 500 - b1) with 500 in VS1 by lia. replace (b1 - b1) with 0 in VS1 by lia. exact VS1. }
    assert (SH2 : SHAD m b2 (cc_gen 100 0)).
    { specialize (VS2 N2). cbn [t3a t3b t3c fst snd] in VS2.
      replace (b2 + 100 - b2) with 100 in VS2 by lia. replace (b2 - b2) with 0 in VS2 by lia. exact VS2. }
    assert (SH3 : SHAD m b3 (cc_gen 100 0)).
    { specialize (VS3 N3). cbn [t3a t3b t3c fst snd] in VS3.
      replace (b3 + 100 - b3) with 100 in VS3 by lia. replace (b3 - b3) with 0 in VS3 by lia. exact VS3. }
    pose proof (addr_cc_disj m p PARSER_SIZE b1 500 O_V1 24 PA SH1 ltac:(lia) ltac:(lia)
                  ltac:(unfold O_V1; lia) ltac:(unfold O_V1, PARSER_SIZE; lia) ltac:(reflexivity) ltac:(reflexivity)) as D1.
    pose proof (addr_cc_disj m p PARSER_SIZE b2 100 O_V2 24 PA SH2 ltac:(lia) ltac:(lia)
                  ltac:(unfold O_V2; lia) ltac:(unfold O_V2, PARSER_SIZE; lia) ltac:(reflexivity) ltac:(reflexivity)) as D2.
    pose proof (addr_cc_disj m p PARSER_SIZE b3 100 O_V3 24 PA SH3 ltac:(lia) ltac:(lia)
                  ltac:(unfold O_V3; lia) ltac:(unfold O_V3, PARSER_SIZE; lia) ltac:(reflexivity) ltac:(reflexivity)) as D3.
    constructor.
    - exact RH.
    - exact LBOWN.
    - split; [exact (proj1 SOWN)|]. rewrite CB, <- SB. exact (proj2 SOWN).
    - exact MEAS.
    - exact MI.
    - exact ERR.
    - exact RAUX.
    - exact AC.
    - exact S0.
    - exact LI.
    - exact (conj AL1 (conj AL2 AL3)).
    - unfold PARSER_SIZE. change (pw_p H w) with p. intros i Hi. destruct (Z_lt_dec i ST_OFF) as [L|L]; [apply PRdef; lia|].
      replace (p + i) with (p + ST_OFF + (i - ST_OFF)) by lia. apply SD. unfold ST_OFF in *. lia.
    - exact PRcons.
    - exact PRuser.
    - exact PRhdr.
    - exact PRins.
    - exact PRhunk.
    - exact (proj2 W0).
    - exact (proj2 W1).
    - exact (proj2 W2).
    - pic. exact (proj2 W3).
    - pic. exact (proj2 W4).
    - pic. exact (proj2 W5).
    - pic. exact FL1.
    - exact FL2.
    - pic. lia.
    - exact PRconsf.
    - exact PRconsm.
    - exact CWR.
    - intros _. exact WMD.
    - pic. exact M1.
    - pic. exact M2.
    - pic. exact M3.
    - pic. apply (pi_vec_opnd s LB m (p + O_V1) b1 HBR RH V1 N1 VD1); unfold O_V1 in *; lia.
    - pic. apply (pi_vec32 s LB m (p + O_V2) b2 HBR RH V2 N2 VD2); unfold O_V2 in *; lia.
    - pic. apply (pi_vec32 s LB m (p + O_V3) b3 HBR RH V3 N3 VD3); unfold O_V3 in *; lia.
    - split; [|exact (conj PA CA)]. unfold pmc_sh, vsh_opnd, vsh32. pic.
      split; [exact U1|]. split; [exact U2|]. split; [exact U3|].
      split; [intros _; exact SH1|]. split; [intros _; exact SH2|]. intros _; exact SH3.
    - reflexivity.
    - intros q k0 Hin. rewrite CB in Hin. destruct Hin as [Ei|[Ei|[Ei|[]]]]; injection Ei; intros; lia.
    - pic. lia.
    - pic. split; [reflexivity|exact He].
    - split; [exact HW|exact HN].
    - unfold pm_bud. pic. unfold OPND_SZ. rewrite ?PmBase.Zlength_nil.
      repeat split; try lia; match goal with Hb : In _ [] |- _ => destruct Hb end.
    - unfold pi_nodes, pi_macct, pi_lacc, pi_m3ok, pi_m2ok. pic. unfold Zlen. cbn [length Z.of_nat].
      repeat split; try lia; apply Forall_nil.
  Qed.
End PiInit.
