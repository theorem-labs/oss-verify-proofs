(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5StepARS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PmModelFactsA PmStep PeStepA PmParKit PeASrcKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeACReset1 PeACEndP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b387c_b3880 Ea0_code_b532c_b5330.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEACEND.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.
Abbreviation st fx R pc M := (@mkst fx R (Z_to_bv 64 pc) M (seg_rom Asan.M.loaded_segments)).

Lemma e_end_stk s : s_stk (e_end s) = s_stk s.
Proof. unfold e_end. destruct (s_estk s) as [|e r]; [reflexivity|]. destruct (ei_indef e); [rewrite eev_stk; reflexivity|]. destruct (ei_cnt e <? ei_len e); [reflexivity|]. destruct (ei_len e <? ei_cnt e); [reflexivity|]. rewrite eev_stk. reflexivity. Qed.
Lemma e_end_pos s : s_pos (e_end s) = s_pos s.
Proof. unfold e_end. destruct (s_estk s) as [|e r]; [reflexivity|]. destruct (ei_indef e); [rewrite eev_pos; reflexivity|]. destruct (ei_cnt e <? ei_len e); [reflexivity|]. destruct (ei_len e <? ei_cnt e); [reflexivity|]. rewrite eev_pos. reflexivity. Qed.
Lemma e_end_done s : s_done (e_end s) = s_done s.
Proof. unfold e_end. destruct (s_estk s) as [|e r]; [reflexivity|]. destruct (ei_indef e); [rewrite eev_done; reflexivity|]. destruct (ei_cnt e <? ei_len e); [reflexivity|]. destruct (ei_len e <? ei_cnt e); [reflexivity|]. rewrite eev_done. reflexivity. Qed.
Lemma e_end_depth s : s_depth (e_end s) = s_depth s.
Proof. unfold e_end. destruct (s_estk s) as [|e r]; [reflexivity|]. destruct (ei_indef e); [rewrite eev_depth; reflexivity|]. destruct (ei_cnt e <? ei_len e); [reflexivity|]. destruct (ei_len e <? ei_cnt e); [reflexivity|]. rewrite eev_depth. reflexivity. Qed.
Lemma r_end_eq X : r_end X = w_stk (tl (s_stk X)) (w_more true (e_end (w_depth (s_depth X - 1) X))).
Proof. unfold r_end. cbv zeta. cbn [s_stk w_more]. rewrite e_end_stk. cbn [s_stk w_depth]. reflexivity. Qed.
Lemma stk_conv_removelast t r : removelast (PEC.stk_conv (t :: r)) = PEC.stk_conv r.
Proof. rewrite PEC.stk_conv_cons, removelast_app by discriminate. cbn. rewrite app_nil_r. reflexivity. Qed.

Definition end_runA (pc0 ra slot sh : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp dp b sz op ov oec : Z),
    0 <= sp < 2 ^ 64 -> 0 <= dp < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 op -> getr R (reg 11) = Z_to_bv 64 ov -> getr R (reg 12) = Z_to_bv 64 oec ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487200 <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - 32) 32 -> 6914048 <= op <= 140737488354944 -> op mod 8 = 0 ->
    (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 48 -> L5.writable RSEGS M op 384 ->
    ((sp - 32) + 32 <= op \/ op + 384 <= (sp - 32)) ->
    6914048 <= ov <= 140737488355272 -> ov mod 8 = 0 -> (2147446784 + 17592186048512 <= ov \/ ov + 56 <= 2147446784) -> L5KA.zeros_at M ((ov / 8) + 2147450880) 7 ->
    L5.writable RSEGS M ov 56 -> ((sp - 32) + 32 <= ov \/ ov + 56 <= (sp - 32)) -> L5.u64_at RSEGS M ov 1258992 -> L5KA.zeros_at M sh 1 ->
    L5.u32_at RSEGS M (op + 12) dp -> 1 <= dp <= 1024 -> (op + 384 <= ov \/ ov + 56 <= op) -> L5.u8_at RSEGS M (op + 16) 0 ->
    L5.u32_at RSEGS M (op + 20) 0 -> L5.u64_at RSEGS M (op + 360) b -> L5.u64_at RSEGS M (op + 368) (b + sz) -> 4096 <= b <= 140737488289792 ->
    64 <= sz <= 32800 -> sz mod 32 = 0 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (op + 12 <= i < op + 12 + 4) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (st fx R pc0 M) (st fx' R' slot M')
      /\ (forall j, In j [3; 4; 5; 6; 7; 12; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 ra /\ getr R' (reg 2) = Z_to_bv 64 (sp - 32) /\ getr R' (reg 8) = Z_to_bv 64 op /\ getr R' (reg 9) = Z_to_bv 64 2147450880
      /\ getr R' (reg 10) = Z_to_bv 64 ov /\ getr R' (reg 11) = Z_to_bv 64 op
      /\ L5.u32_at RSEGS M' (op + 12) (dp - 1)
      /\ L5.u64_at RSEGS M' (sp - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M' (sp - 16) (bv_unsigned (getr R (reg 8)))
      /\ L5.u64_at RSEGS M' (sp - 8) (bv_unsigned (getr R (reg 1))).

Definition end_runB (pc1 : Z) : Prop :=
  forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp b sz op rav s0v s1v : Z),
    0 <= sp < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= rav < 2 ^ 64 -> 0 <= s0v < 2 ^ 64 -> 0 <= s1v < 2 ^ 64 ->
    getr R (reg 2) = Z_to_bv 64 (sp - 32) -> getr R (reg 8) = Z_to_bv 64 op -> getr R (reg 9) = Z_to_bv 64 2147450880 ->
    L5.img_clear M 1253376 1286144 -> L5.u64_at RSEGS M 1317368 2147450880 -> L5.u32_at RSEGS M 1317376 1 -> 140735332487200 <= sp <= 140737488355328 ->
    sp mod 16 = 0 -> L5.writable RSEGS M (sp - 32) 32 -> 6914048 <= op <= 140737488354944 -> op mod 8 = 0 ->
    (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 48 -> L5.writable RSEGS M op 384 ->
    ((sp - 32) + 32 <= op \/ op + 384 <= (sp - 32)) ->
    L5.u64_at RSEGS M (sp - 8) rav -> L5.u64_at RSEGS M (sp - 16) s0v -> L5.u64_at RSEGS M (sp - 24) s1v -> L5.u8_at RSEGS M (op + 16) 0 ->
    L5.u32_at RSEGS M (op + 20) 0 -> L5.u64_at RSEGS M (op + 360) b -> L5.u64_at RSEGS M (op + 368) (b + sz) -> 4096 <= b <= 140737488289792 ->
    64 <= sz <= 32800 -> sz mod 32 = 0 -> L5.writable RSEGS M (op + 8) 8 -> L5.writable RSEGS M (op + 368) 8 ->
    exists fx' R' M', mem_grows M M'
      /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp - 32 + 32) -> ~ (op + 8 <= i < op + 8 + 1) -> ~ (op + 368 <= i < op + 368 + 8) -> M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
      /\ msteps RSEGS (st fx R pc1 M) (st fx' R' 0xaa084 M')
      /\ (forall j, In j [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg j) = getr R (reg j))
      /\ getr R' (reg 1) = Z_to_bv 64 rav /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = Z_to_bv 64 s0v /\ getr R' (reg 9) = Z_to_bv 64 s1v
      /\ getr R' (reg 10) = Z_to_bv 64 (op + 360) /\ getr R' (reg 11) = Z_to_bv 64 (sz / 32)
      /\ L5.u8_at RSEGS M' (op + 8) 1 /\ L5.u64_at RSEGS M' (op + 368) (b + sz - 32).

Lemma srai_reg (R : bvmap 5 word) d : 0 <= d < 2 ^ 63 -> getr R (reg 11) = Z_to_bv 64 d ->
  let R' := regupd R 11%bv (v_srai (getr R 11%bv) (bv_unsigned (5%bv : bv 6))) in
  getr R' (reg 11) = Z_to_bv 64 (d / 32) /\ (forall j, j <> 11%nat -> (j < 32)%nat -> getr R' (reg j) = getr R (reg j)).
Proof.
  intros Hd G R'. split.
  - unfold R'. rewrite <- L5K.rl11. rewrite getr_same by (intros X; discriminate X). rewrite <- L5K.rl11 in G. rewrite G.
    change (bv_unsigned (5%bv : bv 6)) with 5. apply PMARS1.v_srai5_small. exact Hd.
  - intros j Hj Hl. unfold R'. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
    rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E.
    rewrite Z.mod_small in E by lia. lia.
Qed.

Ltac run_tacA A_conc :=
  intros fx R M sp dp b sz op ov oec H1 H2 H3 H4 H5 H6 H7 G2 G10 G11 G12 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22
         K23 K24 K25 K26 K27 K28 K29;
  pose proof (A_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => dp | 34%nat => b | 35%nat => sz | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) as P;
  cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEACENDP.aligned; assumption]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & T11 & T13 & T14 & C12 & S24 & S16 & S8);
  exists fx1, R1, M1;
  split; [exact MG1|];
  split; [intros i Hi N1 N2; apply FRZ1; [exact Hi| exact N1| exact N2]|];
  split; [exact MS1|];
  split; [intros j Hj; apply KS1; cbn in Hj; decompose [or] Hj; try contradiction; subst; inl|];
  split; [exact T1|]; split; [exact T2|]; split; [exact T8|]; split; [exact T9|]; split; [exact T10|]; split; [exact T11|];
  split; [exact C12|]; split; [exact S24|]; split; [exact S16| exact S8].

Lemma ea_runA : end_runA 0xb37a4 0xb381c 0xaae90 2147608257.
Proof. unfold end_runA. run_tacA PEACENDP.aeaA_conc. Qed.

Lemma eo_runA : end_runA 0xb5254 0xb52cc 0xabb0c 2147608264.
Proof. unfold end_runA. run_tacA PEACENDP.aeoA_conc. Qed.

Ltac run_tacB R_conc B_conc SRAI W_S F_S D_S :=
  intros fx R M sp b sz op rav s0v s1v H1 H2 H3 H4 H5 H6 H7 G2 G8 G9 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22 K23;
  pose proof (R_conc fx R M (fun j => match j with 2%nat => sp | 34%nat => b | 35%nat => sz | 36%nat => op | 40%nat => s0v | 41%nat => rav | 42%nat => s1v | _ => 0 end)) as P;
  cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEACENDP.aligned; assumption]);
  destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T5 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & C8);
  pose proof (PMARS1.srai_to fx1 R1 M1 SRAI W_S _ _ _ F_S eq_refl D_S eq_refl ltac:(lia) ltac:(lia)) as MSR;
  destruct (srai_reg R1 sz ltac:(lia) T11) as (T11' & TO);
  set (R1t := regupd R1 11%bv (v_srai (getr R1 11%bv) (bv_unsigned (5%bv : bv 6)))) in MSR, T11', TO;
  assert (Q39 : 2 <= sz / 32 <= 1025) by (clear - K20; split; [apply Z.div_le_lower_bound| apply Z.div_le_upper_bound]; lia);
  assert (Q39r : 0 <= sz / 32 < 2 ^ 64) by (clear - Q39; lia);
  pose proof (B_conc fx1 R1t M1 (fun j => match j with 2%nat => sp | 34%nat => b | 35%nat => sz | 36%nat => op | 39%nat => sz / 32 | 40%nat => s0v | 41%nat => rav | 42%nat => s1v | _ => 0 end)) as P;
  cbn beta iota in P;
  L5SAR.feed P ltac:(first [ assumption | unfold PEACENDP.aligned; assumption
                           | rewrite TO by lia; first [assumption | rewrite (KS1 _) by inl; assumption]
                           | eapply L5.writable_grows; [exact MG1| assumption]
                           | eapply L5C.u64_at_agree; [intros ? ?; apply FRZ1; lia| lia| lia| assumption]
                           | eapply L5C.u8_at_agree; [intros ? ?; apply FRZ1; lia| lia| lia| assumption]
                           | eapply PMF.u32_at_agree; [intros ? ?; apply FRZ1; lia| lia| lia| assumption]
                           | eapply L5KA.zeros_at_agree1; [intros ? ?; apply FRZ1; lia| assumption]
                           | intros ? ?; rewrite FRZ1 by lia; apply K0; lia ]);
  destruct P as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & U1 & U2 & U8 & U9 & U10 & C368);
  exists fx2, R2, M2;
  split; [intros x Hx; apply MG2; apply MG1; exact Hx|];
  split; [intros i Hi N0 N1 N2; rewrite FRZ2 by (first [exact Hi| exact N2]); apply FRZ1; [exact Hi| exact N1]|];
  split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MSR| exact MS2]]|];
  split; [intros j Hj; cbn in Hj; decompose [or] Hj; try contradiction; subst; rewrite (KS2 _) by inl; rewrite TO by lia; rewrite (KS1 _) by inl; reflexivity|];
  split; [exact U1|]; split; [exact U2|]; split; [exact U8|]; split; [exact U9|]; split; [exact U10|];
  split; [rewrite (KS2 11%nat) by inl; exact T11'|];
  split; [apply (L5C.u8_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2; lia| lia| lia| exact C8]| exact C368].

Lemma ea_runB : end_runB 0xb381c.
Proof. unfold end_runB. run_tacB PEACENDP.aeaR_conc PEACENDP.aeaB_conc 0xb38cc W_b387c F_b387c D_b387c. Qed.

Lemma eo_runB : end_runB 0xb52cc.
Proof. unfold end_runB. run_tacB PEACENDP.aeoR_conc PEACENDP.aeoB_conc 0xb537c W_b532c F_b532c D_b532c. Qed.

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMA.ly_as0 L C LY.

Lemma content_keepA' LB FF sp scr W M M' fb p s str sm op :
  L5SAR.ek L ar LB FF sp scr W M M' -> PMKA.wapp W ->
  (forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  PMSPA.aobjA FF (PMSPA.o_is AD fb) 272 -> (forall i, PMSPA.o_is AD fb + 80 <= i < PMSPA.o_is AD fb + 80 + 24 -> L5.outside W i) ->
  incl (PM.vs_own str) LB -> In (PM.sr_qc (PM.p_src s), PM.CHUNK) LB ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PM.iss_at RSEGS AD PMSPA.accA M (PMSPA.o_is AD fb) str sm -> PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M op (PMSPA.o_is AD fb) s ->
  PEC.content_ok RSEGS AD M fb p (PM.p_src s) str sm -> PEC.content_ok RSEGS AD M' fb p (PM.p_src s) str sm.
Proof.
  intros EK WAPP FRB BRB AO OW INCS QIN OB IA PA.
  pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS & _). pose proof VS as (_ & _ & VSF).
  pose proof PA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & SRC & _). pose proof SRC as (_ & _ & _ & _ & _ & _ & _ & G1 & G2 & G3 & _).
  apply (PECFA.content_keepA RSEGS AD L ar LB FF sp scr W M M' EK WAPP FRB BRB fb p s str sm AO OW INCS).
  - intros c n q ->. cbn in VSF. destruct VSF as (_ & _ & _ & Hn & Hc & _ & _ & _). split; [lia|]. apply OB. apply INCS. cbn. left. reflexivity.
  - intros n ->. cbn in VSF. lia.
  - exact QIN.
  - apply OB. exact QIN.
  - exact G1.
  - exact G2.
  - exact G3.
Qed.

Lemma end_core (pc0 ra slot va : Z) :
  0x23ba0 <= va -> va + 8 <= 0x133920 -> va mod 8 = 0 -> L5.ra_ok ra ->
  end_runA pc0 ra slot (va / 8 + 2147450880) -> end_runB ra ->
  PECSA.ann_shrink_spec L ar HI ->
  @PECSPA.eslot_spec SCFG_P RSEGS AD AAD EE L ar HI P unit slot (PECSPA.args_t2 AD) (fun _ => PECSPA.mp_ence) (fun _ _ X => e_end X) ->
  @PECSPA.crun_spec SCFG_P RSEGS AD AAD EE L ar HI P unit pc0 5 (PECSPA.args3 AD) PECSPA.mp_end (fun _ _ X => r_end X).
Proof.
  intros VA1 VA2 VA8 RAOK RUNA RUNB ASH VEND. unfold PECSPA.crun_spec.
  intros PMODE [] fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 ARGS CPRE INCS POK MP NB HB CRED KONT.
  destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 5) with 22528 in *. change (22528 / 8) with 2816 in STKSH.
  pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2). pose proof RAOK as (Hra1 & Hra2).
  destruct ARGS as (A10 & A11 & A12).
  rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
  destruct CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct MP as (PRE & MORE & DONE & HALT & RI & (t0 & rr & HSTK & HCM & HRR & HESTK)).
  pose proof FOK as ((rs & Hfb) & Fal).
  set (op := PMSPA.o_p AD fb) in *. set (ov := PMSPA.o_v AD fb) in *. set (oec := PMSPA.o_ec AD fb) in *. set (ois := PMSPA.o_is AD fb) in *.
  set (osk := PESK.o_sink EE fb) in *.
  assert (Eop : op = fb + 592) by reflexivity. assert (Eov : ov = fb + 496) by reflexivity. assert (Eoec : oec = fb + 1120) by reflexivity.
  assert (Eois : ois = fb + 96) by reflexivity. assert (Eosk : osk = fb + 432) by reflexivity.

  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _).
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6). cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6. change (ff_bytes 5) with 2048 in *.
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in FSAPP. unfold FS_BYTES in *.
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n).
  { intros a n H1 H2. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048. lia. }
  assert (FB8 : forall j, (fb + 8 * j) mod 8 = 0).
  { intros j. pose proof (Z.div_mod fb 2048 ltac:(lia)) as E. rewrite Fal, Z.add_0_r in E. rewrite E.
    replace (2048 * (fb / 2048) + 8 * j) with ((256 * (fb / 2048) + j) * 8) by lia. apply Z_mod_mult. }
  assert (O8 : op mod 8 = 0) by (rewrite Eop; replace (fb + 592) with (fb + 8 * 74) by lia; apply FB8).
  assert (Q8 : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 22528 HH (PMKA.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 sp 22528 HH (PMKA.aobj_of_aobjA FF ov 56 (AOF ov 56 ltac:(lia) ltac:(lia)) Q8) ltac:(lia) ltac:(reflexivity))
    as ((Q1 & Q2 & Q3 & Q4 & Q5) & QBIG & QDEF & QVIS & QSHV & QCL & QSHCL).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
  pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).

  destruct s as [mo dn dp src tb tg vb vk stk].
  cbn [PM.p_src PM.p_stk PM.p_depth PM.p_more PM.p_done PM.p_b PM.p_k PM.p_tb PM.p_tg] in *.
  pose proof PA as (P0 & PD & PC0 & P8 & P9 & P12 & P16 & P20 & PNI & PSRC & P320 & P328 & PC320 & PTB & PVEC & PB1 & PB2 & PB3).
  cbn [PM.p_src PM.p_stk PM.p_depth PM.p_more PM.p_done PM.p_b PM.p_k PM.p_tb PM.p_tg] in P8, P9, P12, PSRC, PTB, PVEC, PB1, PB2, PB3.
  pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
  pose proof (PM.pow2_pos vk ltac:(lia)) as P2k.
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src] in Lmore, Ldone, Ldepth, Lstk, Lpos.
  pose proof (ri_depth X RI) as RDEP. pose proof (ri_dmax X RI) as RDMAX. rewrite HSTK in RDEP. cbn [length] in RDEP.
  assert (HLEN2 : (2 <= length stk)%nat).
  { rewrite Lstk, PEC.stk_conv_length, HSTK. cbn [length]. destruct rr; [exfalso; exact (HRR eq_refl)| cbn; lia]. }
  assert (HLENX : length stk = Datatypes.S (length rr)) by (rewrite Lstk, PEC.stk_conv_length, HSTK; reflexivity).
  assert (DPR : 1 <= dp <= 1024) by (unfold MAX_DEPTH in RDMAX; rewrite Ldepth; lia).
  assert (HN : 2 <= Z.of_nat (length stk) <= 1025) by (unfold MAX_DEPTH in RDMAX; lia).
  assert (SZ32 : (32 * Z.of_nat (length stk)) mod 32 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
  set (LB := PEC.owned (PM.PST mo dn dp src tb tg vb vk stk) en k ++ LBX) in *.
  assert (EPO : LB = (PM.sr_qc src, 16384) :: (vb, 32 * 2 ^ vk) :: (PM.vs_own tb ++ (PEC.enc_own en ++ PESK.sink_own k)) ++ LBX) by reflexivity.
  assert (Ib : In (vb, 32 * 2 ^ vk) LB) by (rewrite EPO; right; left; reflexivity).
  assert (Iq : In (PM.sr_qc src, 16384) LB) by (rewrite EPO; left; reflexivity).
  pose proof (WB _ Ib) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _). cbn [fst snd] in Bb0, Bb1, Bb2, Bb3, Bb4, Bb5.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (PINC : incl (PM.parser_own (PM.PST mo dn dp src tb tg vb vk stk)) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx. }
  assert (SINC : incl (PM.vs_own str) LB) by (unfold LB; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own en) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. left. exact Hx. }
  assert (KINC : incl (PESK.sink_own k) LB).
  { unfold LB, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. right. apply in_or_app. right. exact Hx. }
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; lia).

  assert (CV : forall a m, op <= a -> a + m <= op + 384 -> L5A.avis H a m) by (intros a m X1 X2; eapply L5A.avis_sub; [exact OVIS| lia| lia]).
  assert (CVv : forall a m, ov <= a -> a + m <= ov + 56 -> L5A.avis H a m) by (intros a m X1 X2; eapply L5A.avis_sub; [exact QVIS| lia| lia]).
  assert (U12 : L5.u32_at RSEGS MV (op + 12) dp) by (apply (proj2 (L5A.u32_at_vis H M (op + 12) dp (CV (op + 12) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P12).
  assert (U16 : L5.u8_at RSEGS MV (op + 16) 0) by (apply (proj2 (L5A.u8_at_vis H M (op + 16) 0 (CV (op + 16) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P16).
  assert (U20 : L5.u32_at RSEGS MV (op + 20) 0) by (apply (proj2 (L5A.u32_at_vis H M (op + 20) 0 (CV (op + 20) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P20).
  assert (U360 : L5.u64_at RSEGS MV (op + 360) vb) by (apply (proj2 (L5A.u64_at_vis H M (op + 360) vb (CV (op + 360) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact VC0).
  assert (U368 : L5.u64_at RSEGS MV (op + 368) (vb + 32 * Z.of_nat (length stk))).
  { replace (op + 368) with (op + 360 + 8) by lia. apply (proj2 (L5A.u64_at_vis H M (op + 360 + 8) _ (CV (op + 360 + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact VC8. }
  pose proof EA as (EVT & _ & _ & _ & _ & _ & _ & EDEF & EACC & _). cbn [pe_vt EE PeCLayoutA.EADDR_A] in EVT.
  assert (UVP : L5.u64_at RSEGS MV ov 1258992) by (apply (proj2 (L5A.u64_at_vis H M ov _ (CVv ov 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact EVT).
  assert (IC0 : L5.img_clear MV 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT).
  assert (CSBv : L5.u64_at RSEGS MV 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1317368 2147450880 (VIMG 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
  assert (CUARv : L5.u32_at RSEGS MV 1317376 1) by (apply (proj2 (L5A.u32_at_vis H M 1317376 1 (VIMG 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
  assert (Zop : L5KA.zeros_at MV (op / 8 + SB) 48).
  { apply (L5KA.zeros_at_sub MV (op / 8 + SB) (392 / 8)); [| lia| change (392 / 8) with 49; lia].
    apply (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model op 392 HH (AOF op 392 ltac:(lia) ltac:(lia)) O8); [lia| reflexivity| exact ACCR]. }
  assert (Zov : L5KA.zeros_at MV (ov / 8 + SB) 7).
  { change 7 with (56 / 8). apply (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model ov 56 HH (AOF ov 56 ltac:(lia) ltac:(lia)) Q8); [lia| reflexivity| exact EACC]. }
  assert (ZSL : L5KA.zeros_at MV (va / 8 + 2147450880) 1).
  { apply (PMASK.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model va 1 HH); [lia| lia| exact VA8| lia| right; left; lia]. }
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 22528 32 HH ASTK ltac:(lia)) as (SL32 & SH32 & SWR).
  assert (OWR : L5.writable RSEGS MV op 384).
  { apply (proj2 (L5A.writable_vis H M op 384 OVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact ODEF| lia| lia]. }
  assert (QWR : L5.writable RSEGS MV ov 56).
  { apply (proj2 (L5A.writable_vis H M ov 56 QVIS ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact QDEF| lia| lia]. }
  unfold SB in Zop, Zov.

  destruct (RUNA fx R MV sp dp vb (32 * Z.of_nat (length stk)) op ov oec) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & G1 & G2 & G8 & G9 & G10 & G11 & C12 & S24 & S16 & S8);
    [ clear - SLO SHI SPT; lia | clear - DPR; lia | clear - Bb0 Bb4 SPT P2k; lia | clear - HN; lia | clear - O1 O3; lia | clear - Q1 Q3; lia | clear - Eoec Eop O1 O3; lia
    | exact Rsp | exact A10 | exact A11 | exact A12 | exact IC0 | exact CSBv | exact CUARv | clear - SLO SHI SPT; lia | exact A16 | exact SWR
    | clear - O1 O3; lia | exact O8 | exact OBIG | exact Zop | exact OWR | clear - O2 SLO; lia
    | clear - Q1 Q3; lia | exact Q8 | exact QBIG | exact Zov | exact QWR | clear - Q2 SLO; lia | exact UVP | exact ZSL
    | exact U12 | exact DPR | clear - Eop Eov; lia | exact U16 | exact U20 | exact U360 | exact U368 | clear - Bb0 Bb4 SPT P2k; lia | clear - HN; lia | exact SZ32 |].
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R pc0 R1 slot M1v
           (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (op + 12 <= a < op + 12 + 4)) K HH AM MS1 MG1).
  { intros a Ha Hnw. apply FRZ1; [exact Ha| intros Xa; apply Hnw; left; exact Xa| intros Xa; apply Hnw; right; exact Xa]. }
  { intros a Ha Wa. split.
    - destruct Wa as [Xa|Xa]; unfold aclientw, aclient_g.
      + right; left. split; [clear - Xa SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
        split; [clear - Xa Eop; lia| intros Y; clear - Xa Y Eop; lia].
    - destruct Wa as [Xa|Xa]; [clear - Xa SLO SPT; lia| clear - Xa O1; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.

  assert (C12' : L5.u32_at RSEGS M1 (op + 12) (dp - 1)).
  { apply (proj1 (L5A.u32_at_vis H M1 (op + 12) (dp - 1) (CV (op + 12) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact C12. }
  assert (S8' : L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (reg 1)))).
  { apply (proj1 (L5A.u64_at_vis H M1 (sp - 8) _ (VIS (sp - 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact S8. }
  assert (S16' : L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (reg 8)))).
  { apply (proj1 (L5A.u64_at_vis H M1 (sp - 16) _ (VIS (sp - 16) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact S16. }
  assert (S24' : L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (reg 9)))).
  { apply (proj1 (L5A.u64_at_vis H M1 (sp - 24) _ (VIS (sp - 24) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact S24. }

  set (W1 := [(op + 12, 4)] : list L5.range).
  assert (WAPP1 : PMKA.wapp W1).
  { unfold W1. apply PMKA.wapp_cons; [cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; lia| apply PMKA.wapp_nil]. }
  assert (OUT1 : forall i, ~ (op + 12 <= i < op + 16) -> L5.outside W1 i) by (intros i N r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia).
  assert (OUTB1 : forall q m, In (q, m) LB -> forall i, q <= i < q + m -> L5.outside W1 i).
  { intros q m Hq i Hi. destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH Hq AOP) as [Xa|Xa]; apply OUT1; clear - Xa Hi; lia. }
  assert (EK01 : L5SAR.ek L ar LB FF sp 22528 W1 M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 22528 W1 M M1 (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (op + 12 <= a < op + 12 + 4)) FR1).
    intros a Ha Hc Ho [Xa|Xa].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 22528 a HH SPT Hc) as [(_ & Z2)|Z2]; [apply Z2; clear - Xa; lia| clear - Xa Z2 SLO; lia].
    - apply (Ho (op + 12, 4)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Xa; lia]. }
  assert (DK01 : L5SAR.dk L ar LB FF sp 22528 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  assert (SHM1 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh M M1 a0 n0).
  { intros a0 n0 Ha Hn0 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply FR1; [clear - SX; lia| intros [Y|Y]; clear - Y SX SLO SPT OBIG; lia]. }
  assert (AGB1 : forall q m, In (q, m) LB -> PMFA.agA M M1 q m).
  { intros q m Hin. exact (PMKA.agA_blk L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 BRB q m Hin (OUTB1 q m Hin)). }
  assert (ASTK1 : L5CA.astk ar M1 sp 22528) by exact (L5SAR.astk_grows ar M M1 sp 22528 ASTK MGM1).
  assert (ASTK1c : L5CA.astk ar M1 (sp - 32) 20480).
  { apply (L5SAR.astk_sub ar M M1 sp 22528 32 20480 ASTK MGM1); [lia|lia|lia|]. replace (sp - 32) with (sp + (-2) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
  assert (SP16 : forall j, (sp - 16 * j) mod 8 = 0) by (intros j; apply PMKA.mod16_8'; replace (sp - 16 * j) with (sp + (- j) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
  assert (SZ1 : shadow_zero M1 (sp - 22528) 2816).
  { apply (PMKA.stksh_keepA L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 (sp - 22528) 2816); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact STKSH].
    replace (sp - 22528) with (sp - 16 * 1408) by lia. apply SP16. }
  assert (SZ1c : shadow_zero M1 (sp - 32 - 20480) 2560).
  { apply (PMKA.shadow_zero_sub M1 (sp - 22528) 2816); [| | clear; lia| clear; lia| clear; lia| exact SZ1].
    + replace (sp - 22528) with (sp - 16 * 1408) by lia. apply SP16. + replace (sp - 32 - 20480) with (sp - 16 * 1282) by lia. apply SP16. }

  set (s1 := PM.PST mo dn (dp - 1) src tb tg vb vk stk).
  set (X1 := w_depth (s_depth X - 1) X).
  assert (PAs : PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA M1 op ois s1).
  { apply (PECFA.parser_depth_updA RSEGS AD M M1 op ois (PM.PST mo dn dp src tb tg vb vk stk) (dp - 1) PA); cbn [PM.p_src PM.p_b PM.p_k PM.p_tb].
    - clear - O1; lia.
    - clear - O3; lia.
    - split; [intros i Hi; apply FR1; [clear - Hi O1 O3; lia| intros [Y|Y]; clear - Hi Y O2 SLO; lia]| apply SHM1; clear - O1 O3; lia].
    - split; [intros i Hi; apply FR1; [clear - Hi O1 O3; lia| intros [Y|Y]; clear - Hi Y O2 SLO; lia]| apply SHM1; clear - O1 O3; lia].
    - apply SHM1; clear - O1 O3; lia.
    - intros i Hi. apply MGM1. apply PD. exact Hi.
    - exact C12'.
    - unfold PM.MAX_DEPTH. clear - DPR; lia.
    - destruct (BRB _ Iq) as (X1' & X2'). cbn [fst snd] in X1', X2'. clear - X1'; lia.
    - destruct (BRB _ Iq) as (X1' & X2'). cbn [fst snd] in X1', X2'. unfold PM.CHUNK. clear - X2'; lia.
    - apply AGB1. exact Iq.
    - clear - Bb0; lia.
    - clear - Bb4 SPT; lia.
    - apply AGB1. exact Ib.
    - intros c n0 q E. apply AGB1. apply PINC. unfold PM.parser_own, PM.vs_own. cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]. rewrite E.
      apply in_or_app. right. apply in_or_app. right. left. reflexivity. }
  assert (OUTO1 : forall a m, (a + m <= op \/ op + 384 <= a) -> forall i, a <= i < a + m -> L5.outside W1 i) by (intros a m Xa i Hi; apply OUT1; clear - Xa Hi; lia).
  assert (IA1 : PM.iss_at RSEGS AD PMSPA.accA M1 ois str sm).
  { apply (PMKA.iss_keepA RSEGS AD L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 FRB BRB ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC); [| | exact IA].
    - apply OUTO1. clear - Eop Eois; lia.
    - intros c n0 q E. refine (OUTB1 q c _). apply SINC. unfold PM.vs_own. rewrite E. left. reflexivity. }
  assert (EA1 : PECA.enc_atA RSEGS EE L ar M1 ov fb en).
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA].
    - apply OUTO1. clear - Eop Eov; lia.
    - intros Hp. refine (OUTB1 _ _ _). apply EINC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  assert (VREF1 : L5.u64_at RSEGS M1 (op + 384) ov).
  { apply (PMKA.u64_keepA RSEGS L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply OUTO1. clear; lia. }
  assert (SKA1 : PESKA.sink_atA RSEGS L ar P M1 osk k).
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA].
    - apply OUTO1. clear - Eop Eosk; lia.
    - intros Hp. refine (OUTB1 _ _ _). apply KINC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  assert (SDEP : forall W, (forall i, ~ (op <= i < op + 384) -> L5.outside W i) -> forall a, PMST.dep AD a -> hl_img_lo L <= a < hl_img_hi L /\ ~ hl_rt_static L a /\ L5.outside W a).
  { intros W OUT a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUT. clear - DI O1; lia. }
  assert (BASE1 : PMSTA.base_okA RSEGS AD M1).
  { change (PMSTA.base_okA RSEGS PMA.AD M1). apply (PMASK.base_keep L ar C LY LB FF sp 22528 W1 M M1 EK01); [| exact BASE]. intros a Ha. apply OUT1. clear - Ha O1; lia. }
  assert (ERR1 : PESTA.err_okA RSEGS AD AAD EE M1 e).
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LB FF sp 22528 W1 M M1 EK01 e PECSA.addrs_wf_A); [| exact ERR]. refine (SDEP W1 _). intros i N. apply OUT1. clear - N; lia. }
  assert (CONT1 : PEC.content_ok RSEGS AD M1 fb p src str sm).
  { apply (content_keepA' LB FF sp 22528 W1 M M1 fb p (PM.PST mo dn dp src tb tg vb vk stk) str sm op EK01 WAPP1 FRB BRB (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC| exact Iq| | exact IA| exact PA| exact CONT].
    - fold ois. apply OUTO1. clear - Eop Eois; lia.
    - intros q m Hq. exact (OUTB1 q m Hq). }
  assert (ECS1 : PECA.ec_stateA RSEGS AD M1 fb (s_ec X) cat).
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 FRB fb (s_ec X) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTO1. clear - Eop Eoec; lia. }
  assert (ACC1 : PMSPA.accA M1 op PECA.RDR_BYTES) by exact (PMKA.acc_keepA' L ar LB FF sp 22528 W1 M M1 EK01 WAPP1 FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACCR).
  assert (CL1 : PEC.clink p X1 s1 sm en k).
  { unfold PEC.clink, X1, s1, w_depth. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
    split; [exact Lmore|]. split; [exact Ldone|]. split; [lia|]. split; [exact Lstk|]. split; [exact Lpos|].
    split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
  assert (MPE : PECSPA.mp_ence p X1).
  { unfold PECSPA.mp_ence, PECSPA.mp_enc, X1, w_depth. cbn [s_lo s_hi s_bad s_estk s_edepth]. destruct PRE as (_ & _ & Plh & Pbad & Ped & Peok).
    split; [| unfold MAX_DEPTH in *; lia]. split; [exact Plh|]. split; [exact Pbad|]. split; [exact Peok|]. unfold MAX_DEPTH in *. lia. }
  assert (NB1 : s_bad (e_end X1) = false) by (rewrite r_end_eq in NB; cbn [s_bad w_stk w_more] in NB; exact NB).
  assert (HB1 : PESKA.spa_hb P (s_hi (e_end X1))) by (rewrite r_end_eq in HB; cbn [s_hi w_stk w_more] in HB; exact HB).

  pose proof (PMA.ly_cost L C LY) as (KPM & BLIN & BOV).
  assert (PPN : 0 <= fst (PM.pot_parser (PMSPA.HV L ar) s1) /\ 0 <= snd (PM.pot_parser (PMSPA.HV L ar) s1)).
  { pose proof PTB as (_ & _ & TBF). destruct TBOK as (TG1 & TG2 & _).
    unfold PM.pot_parser, PM.credit_add, PM.pot_stack, PM.pot_text, s1. cbn [fst snd PM.p_k PM.p_tb PM.p_tg].
    unfold PMSPA.HV, LibIfaceAB.heap_view. cbn [HeapIface.hl_k_per_malloc HeapIface.hl_b_overhead]. rewrite KPM, BOV.
    assert (CAPB : 0 <= PM.vs_cap tb <= 2 ^ 27) by (destruct tb as [n1|c1 n1 q1]; cbn [PM.vs_cap] in *; [lia| destruct TBF as (_ & _ & _ & _ & Hc1 & _); lia]).
    pose proof (PM.pow2_pos (vk + 1) ltac:(lia)) as P2a. assert (P2b : 2 ^ (vk + 1) <= 2 ^ 12) by (apply Z.pow_le_mono_r; lia).
    clear - CAPB P2a P2b Hk TG1. split; nia. }
  assert (CREDe : PMSP.credit_le (PECA.pot_encA L ar P en k) cr).
  { unfold PMSP.credit_le, PECA.pot_allA, PECA.pot_encA, PEC.credit_add, PMSPA.scA in CRED |- *. cbn [fst snd] in CRED |- *.
    change (PM.pot_parser (PMSPA.HV L ar) (PM.PST mo dn dp src tb tg vb vk stk)) with (PM.pot_parser (PMSPA.HV L ar) s1) in CRED. clear - CRED PPN BLIN. nia. }

  apply (VEND PMODE tt fx1 R1 M1 model1 K LBX FF LK Aw cr (sp - 32) ra fb cat p X1 s1 str sm en k e HH1 AM1 K0).
  { split; [rewrite L5K.rl1; exact G1|]. split; [exact RAOK|]. split; [rewrite L5K.rl2; exact G2|].
    split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. split; [exact ASTK1c|]. change (20480 / 8) with 2560. exact SZ1c. }
  { intros kk Hkk. specialize (FRM kk Hkk). clear - FRM; lia. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  { exact FOK. }
  { replace (sp - 32) with (sp + (-1) * 32) by lia. rewrite Z_mod_plus_full. exact SP32. }
  { rewrite L5K.rl10. exact G10. }
  { unfold PECSPA.args_t2. rewrite L5K.rl12. rewrite (KS1 12%nat) by inl. exact A12. }
  { split; [exact PAs|]. split; [exact IA1|]. split; [exact EA1|]. split; [exact VREF1|]. split; [exact SKA1|].
    split; [exact BASE1|]. split; [exact ERR1|]. split; [exact TBOK|]. split; [exact CONT1|]. split; [exact CL1|]. split; [exact ECS1|]. split; [exact ECI| exact ACC1]. }
  { exact INCS. }
  { exact POK. }
  { exact MPE. }
  { exact NB1. }
  { exact HB1. }
  { exact CREDe. }
  intros fx2 R2 M2 model2 LK2 Aw2 en2 k2 e2 cr2 RP2 CPRE2 EIMP2 HP2 CK2 MRT2 INCLK2 INCAw2 AM2 HH2.

  change (PMSPA.pm_scr 4) with 20480 in HP2.
  destruct CPRE2 as (PA2 & IA2 & EA2 & VREF2 & SKA2 & BASE2 & ERR2 & TBOK2 & CONT2 & CL2 & ECS2 & ECI2 & ACC2).
  pose proof AM2 as (Mh2 & MI2).
  set (LB2 := PEC.owned s1 en2 k2 ++ LBX) in HH2.
  set (LBc := (PM.sr_qc src, 16384) :: (PM.vs_own tb ++ (PEC.enc_own en2 ++ PESK.sink_own k2)) ++ LBX).
  assert (EPO2 : LB2 = (PM.sr_qc src, 16384) :: (vb, 32 * 2 ^ vk) :: (PM.vs_own tb ++ (PEC.enc_own en2 ++ PESK.sink_own k2)) ++ LBX) by reflexivity.
  assert (INCc : incl LBc LB2) by (intros x Hx; rewrite EPO2; destruct Hx as [<-|Hx]; [left; reflexivity| right; right; exact Hx]).
  assert (INCx : incl LBX LBc) by (intros x Hx; right; apply in_or_app; right; exact Hx).
  assert (BRB2 : forall x, In x LB2 -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH2).
  assert (BRBc : forall x, In x LBc -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by (intros x Hx; apply BRB2; apply INCc; exact Hx).
  assert (Iq2 : In (PM.sr_qc src, 16384) LBc) by (left; reflexivity).
  assert (Ib2 : In (vb, 32 * 2 ^ vk) LB2) by (rewrite EPO2; right; left; reflexivity).
  assert (EINC2 : incl (PEC.enc_own en2) LBc) by (intros x Hx; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC2 : incl (PESK.sink_own k2) LBc) by (intros x Hx; right; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (SINC2 : incl (PM.vs_own str) LBc) by (intros x Hx; apply INCx; apply INCS; exact Hx).
  assert (TINC2 : forall c n0 q, tb = PM.VLong c n0 q -> In (q, c) LBc).
  { intros c n0 q E. right. apply in_or_app. left. apply in_or_app. left. unfold PM.vs_own. rewrite E. left. reflexivity. }
  assert (VBA : vb + 32 * 2 ^ vk <= op \/ op + 384 <= vb) by exact (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ vb (32 * 2 ^ vk) op 384 HH2 Ib2 AOP).
  assert (ASTK2 : L5CA.astk ar M2 sp 22528).
  { apply (PMKA.astk_after_ahpres L ar (PM.parser_own s1 ++ LBX) FF M1 M2 sp 22528 (sp - 32) 20480 (PEC.W_enc AD EE fb) ASTK1 HP2); [clear; lia| clear; lia| clear; lia| exact STOP]. }

  assert (OWEs : forall a, sp - 22528 <= a < sp -> L5.outside (PEC.W_enc AD EE fb) a).
  { intros a Ha r0 Hr. unfold PEC.W_enc, PMSP.err_W in Hr. cbn [app] in Hr. unfold L5.in_rng.
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PMSP.o_v, PMSP.o_ec, PESK.o_sink;
      cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A]; clear - Ha F2 FSCEIL SLO SPT; lia. }
  assert (WAPPe : PMKA.wapp (PEC.W_enc AD EE fb)).
  { unfold PEC.W_enc, PMSP.err_W. cbn [app]. unfold PMSP.o_v, PMSP.o_ec, PESK.o_sink.
    cbn [pa_off_v pa_off_ec pe_off_sink pa_errcat_guard pa_atexit PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A].
    repeat apply PMKA.wapp_cons; [..|apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - F1 F2 FSAPP; lia. }
  assert (EK12e : L5SAR.ek L ar LBX FF sp 22528 (PEC.W_enc AD EE fb) M1 M2).
  { apply (L5SAR.ek_callee L ar LBX (PM.parser_own s1) FF [] sp 22528 (sp - 32) 20480 (PEC.W_enc AD EE fb) (PEC.W_enc AD EE fb) M1 M2 HP2); [clear; lia| clear; lia|].
    intros a _ O. exact O. }
  assert (SZ2 : shadow_zero M2 (sp - 22528) 2816).
  { apply (PMKA.stksh_keepA L ar LBX FF sp 22528 (PEC.W_enc AD EE fb) M1 M2 EK12e WAPPe (sp - 22528) 2816); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact SZ1].
    replace (sp - 22528) with (sp - 16 * 1408) by lia. apply SP16. }
  assert (FRAME12 : forall a, sp - 32 <= a < sp -> M2 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
  { intros a Ha. pose proof HP2 as (P2 & _). apply P2. split; [clear - Ha SLO SHI SPT; lia|]. split.
    - unfold aclient, aclient_g. right; left. split; [clear - Ha SLO SHI SPT; lia| intros Y; clear - Ha Y; lia].
    - apply OWEs. clear - Ha; lia. }

  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 HH2) as (_ & VIS2 & VIMG2 & _).
  set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 op 384 sp 22528 HH2 (PMKA.aobj_of_aobjA FF op 384 AOP O8) ltac:(lia) ltac:(reflexivity))
    as (_ & _ & ODEF2 & OVIS2 & _).
  pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH2) as ST2. rewrite (L5A.aly_segs L C LYa) in ST2.
  pose proof (L5A.statics_facts L C M2 LYa ST2) as (GOT2 & CSB2 & CUAR2 & _).
  pose proof PA2 as (P0b & PD2 & PC0b & P8b & P9b & P12b & P16b & P20b & PNIb & PSRCb & P320b & P328b & PC320b & PTBb & PVEC2 & _).
  cbn [PM.p_src PM.p_stk PM.p_depth PM.p_more PM.p_done PM.p_b PM.p_k PM.p_tb PM.p_tg s1] in P12b, P16b, P20b, PSRCb, PTBb, PVEC2.
  pose proof PVEC2 as (VC0b & VC8b & VC16b & _ & _ & _ & DBb & CBb & ANb & ELb).
  assert (CV2 : forall a m, op <= a -> a + m <= op + 384 -> L5A.avis H2 a m) by (intros a m X1' X2'; eapply L5A.avis_sub; [exact OVIS2| lia| lia]).
  assert (U16b : L5.u8_at RSEGS MV2 (op + 16) 0) by (apply (proj2 (L5A.u8_at_vis H2 M2 (op + 16) 0 (CV2 (op + 16) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P16b).
  assert (U20b : L5.u32_at RSEGS MV2 (op + 20) 0) by (apply (proj2 (L5A.u32_at_vis H2 M2 (op + 20) 0 (CV2 (op + 20) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P20b).
  assert (U360b : L5.u64_at RSEGS MV2 (op + 360) vb) by (apply (proj2 (L5A.u64_at_vis H2 M2 (op + 360) vb (CV2 (op + 360) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact VC0b).
  assert (U368b : L5.u64_at RSEGS MV2 (op + 368) (vb + 32 * Z.of_nat (length stk))).
  { replace (op + 368) with (op + 360 + 8) by lia. apply (proj2 (L5A.u64_at_vis H2 M2 (op + 360 + 8) _ (CV2 (op + 360 + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact VC8b. }
  assert (IC2 : L5.img_clear MV2 1253376 1286144) by (apply L5A.img_clear_mrestrict; exact GOT2).
  assert (CSB2v : L5.u64_at RSEGS MV2 1317368 2147450880) by (apply (proj2 (L5A.u64_at_vis H2 M2 1317368 2147450880 (VIMG2 1317368 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB2).
  assert (CUAR2v : L5.u32_at RSEGS MV2 1317376 1) by (apply (proj2 (L5A.u32_at_vis H2 M2 1317376 1 (VIMG2 1317376 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR2).
  assert (Zop2 : L5KA.zeros_at MV2 (op / 8 + 2147450880) 48).
  { apply (L5KA.zeros_at_sub MV2 (op / 8 + SB) (392 / 8)); [| unfold SB; lia| change (392 / 8) with 49; unfold SB; lia].
    apply (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 model2 op 392 HH2 (AOF op 392 ltac:(lia) ltac:(lia)) O8); [lia| reflexivity| exact ACC2]. }
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK2 cr2 Aw2 M2 model2 sp 22528 32 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2).
  assert (OWR2 : L5.writable RSEGS MV2 op 384).
  { apply (proj2 (L5A.writable_vis H2 M2 op 384 OVIS2 ltac:(lia) ltac:(lia))). apply (L5C.writable_of_defined RSEGS); [exact ODEF2| lia| lia]. }
  assert (W8 : L5.writable RSEGS MV2 (op + 8) 8) by (apply (L5.writable_sub RSEGS MV2 op 384 (op + 8) 8 OWR2); clear; lia).
  assert (W368 : L5.writable RSEGS MV2 (op + 368) 8) by (apply (L5.writable_sub RSEGS MV2 op 384 (op + 368) 8 OWR2); clear; lia).
  assert (SVV : forall a v, sp - 32 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1 a v -> L5.u64_at RSEGS MV2 a v).
  { intros a v Ha1 Ha2 SV. apply (proj2 (L5A.u64_at_vis H2 M2 a v (VIS2 a 8 ltac:(clear - Ha1 SLO; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SLO SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    apply (L5C.u64_at_agree RSEGS M1 M2); [intros i Hi; apply FRAME12; clear - Hi Ha1 Ha2; lia| clear - Ha1 SLO SPT; lia| clear - Ha2 SHI SPT; lia| exact SV]. }
  pose proof (SVV (sp - 8) _ ltac:(lia) ltac:(lia) S8') as Y8. pose proof (SVV (sp - 16) _ ltac:(lia) ltac:(lia) S16') as Y16. pose proof (SVV (sp - 24) _ ltac:(lia) ltac:(lia) S24') as Y24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9.
  assert (G2b : getr R2 (reg 2) = Z_to_bv 64 (sp - 32)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact G2).
  assert (G8b : getr R2 (reg 8) = Z_to_bv 64 op) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact G8).
  assert (G9b : getr R2 (reg 9) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; exact G9).
  destruct (RUNB fx2 R2 MV2 sp vb (32 * Z.of_nat (length stk)) op (bv_unsigned (getr R (reg 1))) (bv_unsigned (getr R (reg 8))) (bv_unsigned (getr R (reg 9))))
    as (fx3 & R3 & M3v & MG3 & FRZ3 & MS3 & KS3 & T1 & T2 & T8 & T9 & T10 & T11 & C8 & C368);
    [ clear - SLO SHI SPT; lia | clear - Bb0 Bb4 SPT P2k; lia | clear - HN; lia | clear - O1 O3; lia | exact B1 | exact B8 | exact B9
    | exact G2b | exact G8b | exact G9b | exact IC2 | exact CSB2v | exact CUAR2v | clear - SLO SHI SPT; lia | exact A16 | exact SWR2
    | clear - O1 O3; lia | exact O8 | exact OBIG | exact Zop2 | exact OWR2 | clear - O2 SLO; lia
    | exact Y8 | exact Y16 | exact Y24 | exact U16b | exact U20b | exact U360b | exact U368b | clear - Bb0 Bb4 SPT P2k; lia | clear - HN; lia | exact SZ32
    | exact W8 | exact W368 |].
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LB2 FF LK2 cr2 Aw2 M2 model2 fx2 fx3 R2 ra R3 0xaa084 M3v
           (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (op + 8 <= a < op + 8 + 1) \/ (op + 368 <= a < op + 368 + 8)) K HH2 AM2 MS3 MG3).
  { intros a Ha Hnw. apply FRZ3; [exact Ha| intros Xa; apply Hnw; left; exact Xa| intros Xa; apply Hnw; right; left; exact Xa| intros Xa; apply Hnw; right; right; exact Xa]. }
  { intros a Ha Wa. split.
    - destruct Wa as [Xa|Xa]; unfold aclientw, aclient_g.
      + right; left. split; [clear - Xa SLO SHI SPT; lia| intros Y; clear - Y; lia].
      + do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
        split; [clear - Xa Eop; lia| intros Y; clear - Xa Y Eop; lia].
    - destruct Wa as [Xa|Xa]; [clear - Xa SLO SPT; lia| clear - Xa O1; lia]. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.

  assert (C8' : L5.u8_at RSEGS M3 (op + 8) 1).
  { apply (proj1 (L5A.u8_at_vis H2 M3 (op + 8) 1 (CV2 (op + 8) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS3. exact C8. }
  assert (C368' : L5.u64_at RSEGS M3 (op + 368) (vb + 32 * Z.of_nat (length stk) - 32)).
  { apply (proj1 (L5A.u64_at_vis H2 M3 (op + 368) _ (CV2 (op + 368) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS3. exact C368. }
  set (W3 := [(op + 8, 1); (op + 368, 8)] : list L5.range).
  assert (WAPP3 : PMKA.wapp W3).
  { unfold W3. repeat apply PMKA.wapp_cons; [..|apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - OBIG; lia. }
  assert (OUT3 : forall i, ~ (op + 8 <= i < op + 9) -> ~ (op + 368 <= i < op + 376) -> L5.outside W3 i).
  { intros i N1 N2 r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
  assert (OUTO3 : forall a m, (a + m <= op \/ op + 384 <= a) -> forall i, a <= i < a + m -> L5.outside W3 i) by (intros a m Xa i Hi; apply OUT3; clear - Xa Hi; lia).
  assert (OUTBc : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> L5.outside W3 i).
  { intros q m Hq i Hi. destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HH2 (INCc _ Hq) AOP) as [Xa|Xa]; apply OUT3; clear - Xa Hi; lia. }
  assert (OCLc : forall a, op <= a < op + 384 -> aclient L ar LBc FF sp 22528 a).
  { intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - Ha Eop; lia| intros Y; clear - Ha Eop Y; lia]. }
  assert (HH2s : ri_inv HI (PM.vec_own vb vk ++ LBc) FF LK2 cr2 Aw2 M2 (vml_of model2)).
  { pose proof HH2 as HH2'. rewrite EPO2 in HH2'. exact (PMARS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH2'). }
  assert (EK23 : L5SAR.ek L ar LBc FF sp 22528 W3 M2 M3).
  { apply (L5SAR.ek_piece L ar LBc FF sp 22528 W3 M2 M3 (fun a => (sp - 32 <= a < sp - 32 + 32) \/ (op + 8 <= a < op + 8 + 1) \/ (op + 368 <= a < op + 368 + 8)) FR3).
    intros a Ha Hc Ho [Xa|[Xa|Xa]].
    - destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK2 cr2 Aw2 M2 _ sp 22528 a HH2s SPT (L5SAR.aclient_appb L ar LBc (PM.vec_own vb vk) FF sp 22528 a Hc))
        as [(_ & Z2)|Z2]; [apply Z2; clear - Xa; lia| clear - Xa Z2 SLO; lia].
    - apply (Ho (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Xa; lia].
    - apply (Ho (op + 368, 8)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - Xa; lia]. }
  assert (SHM3 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh M2 M3 a0 n0).
  { intros a0 n0 Ha Hn0 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
    apply FR3; [clear - SX; lia| intros [Y|[Y|Y]]; clear - Y SX SLO SPT OBIG; lia]. }
  assert (AGB3 : L5C.agree_on M2 M3 vb (32 * 2 ^ vk)).
  { intros i Hi. apply FR3; [clear - Hi Bb0 Bb4 SPT; lia| intros [Y|[Y|Y]]; [clear - Y Hi Bb4 SLO; lia| clear - Y Hi VBA; lia| clear - Y Hi VBA; lia]]. }
  assert (ASTK3 : L5CA.astk ar M3 sp 22528) by exact (L5SAR.astk_grows ar M2 M3 sp 22528 ASTK2 MGM3).
  assert (ASTK3c : L5CA.astk ar M3 sp 12288).
  { pose proof (L5SAR.astk_sub ar M2 M3 sp 22528 0 12288 ASTK2 MGM3 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact A16)) as Xa.
    rewrite Z.sub_0_r in Xa. exact Xa. }
  assert (SZ3 : shadow_zero M3 (sp - 22528) 2816).
  { apply (PMKA.stksh_keepA L ar LBc FF sp 22528 W3 M2 M3 EK23 WAPP3 (sp - 22528) 2816); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact SZ2].
    replace (sp - 22528) with (sp - 16 * 1408) by lia. apply SP16. }
  assert (SZ3c : shadow_zero M3 (sp - 12288) 1536).
  { apply (PMKA.shadow_zero_sub M3 (sp - 22528) 2816); [| | clear; lia| clear; lia| clear; lia| exact SZ3].
    + replace (sp - 22528) with (sp - 16 * 1408) by lia. apply SP16. + replace (sp - 12288) with (sp - 16 * 768) by lia. apply SP16. }

  unfold PECSA.ann_shrink_spec, PMSAX.ann_shrink_spec in ASH. cbn [paa_ann_shrink PeCLayoutA.CAADDR_A] in ASH.
  assert (LRM : length (removelast stk) = (length stk - 1)%nat) by (apply PMPK.removelast_len; clear - HLEN2; lia).
  assert (HH3s : ri_inv HI (PM.vec_own vb vk ++ LBc) FF LK2 cr2 Aw2 M3 (vml_of model3)).
  { rewrite EPO2 in HH3. exact (PMARS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH3). }
  apply (ASH fx3 R3 M3 model3 K LBc FF LK2 Aw2 cr2 (op + 360) vb vk (Z.of_nat (length stk)) (removelast stk) sp r HH3s AM3 K0).
  { split; [rewrite L5K.rl1; rewrite T1; rewrite Z_to_bv_bv_unsigned; exact Rra|]. split; [exact RAok|]. split; [rewrite L5K.rl2; exact T2|].
    split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 3 RP2) by inl; rewrite (KS1 3%nat) by inl; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 4 RP2) by inl; rewrite (KS1 4%nat) by inl; exact Rtp|].
    change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK3c|]. change (12288 / 8) with 1536. exact SZ3c. }
  { exact FRS. }
  { rewrite L5K.rl10. exact T10. }
  { rewrite L5K.rl11. rewrite T11. f_equal. rewrite Z.mul_comm. apply Z.div_mul. clear; lia. }
  { apply AOF; clear - Eop; lia. }
  { replace (op + 360) with (op + 45 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
  { apply (PMKA.acc_keepA' L ar LBc FF sp 22528 W3 M2 M3 EK23 WAPP3 FRB (op + 360) 24 (AOF (op + 360) 24 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
    intros a Ha. apply PC320b. clear - Ha; lia. }
  { rewrite LRM. clear - HN Hlen; lia. }
  { apply (PMKA.u64_keepA RSEGS L ar LBc FF sp 22528 W3 M2 M3 EK23 WAPP3 FRB (op + 360) vb (AOF (op + 360) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VC0b].
    intros i Hi r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi; lia. }
  { rewrite LRM. replace (op + 360 + 8) with (op + 368) by lia. replace (vb + 32 * Z.of_nat (length stk - 1)) with (vb + 32 * Z.of_nat (length stk) - 32) by (clear - HLEN2; lia). exact C368'. }
  { apply (PMKA.u64_keepA RSEGS L ar LBc FF sp 22528 W3 M2 M3 EK23 WAPP3 FRB (op + 360 + 16) _ (AOF (op + 360 + 16) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VC16b].
    intros i Hi r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi; lia. }
  { clear - Hk; lia. }
  { exact Hal. }
  { intros i Hi. apply MGM3. apply DBb. exact Hi. }
  { apply (PMFA.accA_agree M2 M3); [apply SHM3; clear - Bb0 Bb4 SPT Hlen P2k; lia| exact CBb]. }
  { apply (PMFA.annA_agree M2 M3); [apply PMKA.mod16_8'; exact Hal| clear - Hlen P2k; lia| | apply SHM3; clear - Bb0 Bb4 SPT; lia| exact ANb].
    replace (32 * 2 ^ vk) with ((4 * 2 ^ vk) * 8) by lia. apply Z_mod_mult. }
  { intros i Hi. rewrite LRM in Hi. rewrite PMPK.nth_removelast_lt by (rewrite LRM; exact Hi).
    assert (Hi' : Z.of_nat i < Z.of_nat (length stk) - 1) by (clear - Hi HLEN2; lia).
    apply (PMF.pstate_at_agree RSEGS M2 M3); [clear - Bb0; lia| clear - Hi' Bb4 SPT Hlen P2k; lia| | apply ELb; clear - Hi HLEN2; lia].
    eapply (L5C.agree_on_sub M2 M3 vb (32 * 2 ^ vk)); [exact AGB3| clear; lia| clear - Hi' Hlen P2k; lia]. }
  intros fx4 R4 M4 model4 LK4 Aw4 RP4 VEC4 ACC4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 0) with 12288 in HP4.

  assert (ASTK4 : L5CA.astk ar M4 sp 22528) by (apply (PMKA.astk_after_ahpres L ar LBc FF M3 M4 sp 22528 sp 12288 [] ASTK3 HP4); [clear; lia| clear; lia| clear; lia| exact STOP]).
  assert (EK34 : L5SAR.ek L ar LBc FF sp 22528 W3 M3 M4) by (apply (L5SAR.ek_callee L ar LBc [] FF [] sp 22528 sp 12288 W3 [] M3 M4 HP4); [clear; lia| clear; lia| intros a _ _ r0 []]).
  assert (EK34n : L5SAR.ek L ar LBc FF sp 22528 [] M3 M4) by (apply (L5SAR.ek_callee L ar LBc [] FF [] sp 22528 sp 12288 [] [] M3 M4 HP4); [clear; lia| clear; lia| intros a _ _ r0 []]).
  pose proof (L5SAR.ek_trans L ar LBc FF sp 22528 W3 M2 M3 M4 EK23 EK34) as EK24.
  assert (DK24 : L5SAR.dk L ar LBc FF sp 22528 M2 M4).
  { apply (L5SAR.dk_trans L ar LBc FF sp 22528 M2 M3 M4); [apply L5SAR.dk_grows; exact MGM3|].
    apply (L5SAR.dk_callee L ar LBc [] FF [] sp 22528 sp 12288 [] M3 M4 HP4); clear; lia. }
  destruct CL2 as (L2more & L2done & L2depth & L2stk & L2pos & L2estk & L2edepth & L2z & L2bad).
  cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src s1] in L2more, L2done, L2depth, L2stk, L2pos.

  assert (OW1 : forall a, L5.outside (PEC.W_crun AD EE fb) a -> L5.outside W1 a).
  { intros a O r0 [<-|[]] Xa. unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W in O. cbn [app] in O.
    apply (O (PMSP.o_p AD fb + 8, 8)); [left; reflexivity|].
    unfold L5.in_rng in *. cbn [fst snd] in *. unfold PMSP.o_p. cbn [pa_off_p PeCLayoutA.CADDR_A]. clear - Xa Eop. lia. }
  assert (OW3 : forall a, L5.outside (PEC.W_crun AD EE fb) a -> L5.outside W3 a).
  { intros a O r0 [<-|[<-|[]]] Xa; unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W in O; cbn [app] in O.
    - apply (O (PMSP.o_p AD fb + 8, 8)); [left; reflexivity|].
      unfold L5.in_rng in *. cbn [fst snd] in *. unfold PMSP.o_p. cbn [pa_off_p PeCLayoutA.CADDR_A]. clear - Xa Eop. lia.
    - apply (O (PMSP.o_vec AD fb, 24)); [do 5 right; left; reflexivity|].
      unfold L5.in_rng in *. cbn [fst snd] in *. unfold PMSP.o_vec, PMSP.o_p. cbn [pa_off_p PeCLayoutA.CADDR_A]. clear - Xa Eop. lia. }
  assert (OWE : forall a, L5.outside (PEC.W_crun AD EE fb) a -> L5.outside (PEC.W_enc AD EE fb) a).
  { intros a O r0 Hr. apply O. unfold PEC.W_enc, PMSP.err_W in Hr. cbn [app] in Hr. unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W. cbn [app].
    destruct Hr as [<-|[<-|[<-|[<-|[<-|[]]]]]];
      [ do 9 right; left; reflexivity | do 10 right; left; reflexivity | do 6 right; left; reflexivity | do 7 right; left; reflexivity | do 8 right; left; reflexivity ]. }
  assert (INCLx : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).

  apply (KONT fx4 R4 M4 model4 LK4 Aw4 (PM.PST 1 dn (dp - 1) src tb tg vb vk (removelast stk)) sm en2 k2 e2 cr2).
  -
    apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    rewrite (L5SAR.cs_of_preserved R3 R4 _ RP4 Hj').
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite T2; exact (eq_sym Rsp) | rewrite T8; apply Z_to_bv_bv_unsigned | rewrite T9; apply Z_to_bv_bv_unsigned
                                            | rewrite (KS3 _) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; apply KS1; inl ] |]). destruct Hj.
  -
    cbn beta. rewrite r_end_eq. fold X1.
    split.
    { apply (PECFA.parser_morepop_updA RSEGS AD M2 M4 op ois s1 PA2); cbn [PM.p_stk PM.p_src PM.p_b PM.p_k PM.p_tb s1].
      + clear - O1; lia.
      + clear - O3; lia.
      + apply (PMKA.agA_obj L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). intros i Hi. apply OUT3; clear - Hi; lia.
      + apply (PMKA.agA_obj L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB (op + 9) 7 (AOF (op + 9) 7 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). intros i Hi. apply OUT3; clear - Hi; lia.
      + apply (PMKA.agA_obj L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB (op + 16) 344 (AOF (op + 16) 344 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). intros i Hi. apply OUT3; clear - Hi; lia.
      + exact (PMKA.agsh_obj L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB op 384 AOP).
      + intros i Hi. apply DK24; [clear - Hi O1 O3; lia| apply OCLc; clear - Hi; lia| apply PD2; exact Hi].
      + apply (PMKA.u8_keepA RSEGS L ar LBc FF sp 22528 [] M3 M4 EK34n PMKA.wapp_nil FRB (op + 8) 1 (AOF (op + 8) 1 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [intros i _ r0 []| exact C8'].
      + exact VEC4.
      + destruct (BRBc _ Iq2) as (X1' & X2'). cbn [fst snd] in X1', X2'. clear - X1'; lia.
      + destruct (BRBc _ Iq2) as (X1' & X2'). cbn [fst snd] in X1', X2'. unfold PM.CHUNK. clear - X2'; lia.
      + apply (PMKA.agA_blk L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 BRBc _ 16384 Iq2). exact (OUTBc _ 16384 Iq2).
      + intros c n0 q E. apply (PMKA.agA_blk L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 BRBc q c (TINC2 c n0 q E)). exact (OUTBc q c (TINC2 c n0 q E)). }
    split.
    { apply (PMKA.iss_keepA RSEGS AD L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB BRBc ois str sm (AOF ois 272 ltac:(lia) ltac:(lia)) SINC2); [| | exact IA2].
      - apply OUTO3. clear - Eop Eois; lia.
      - intros c n0 q E. refine (OUTBc q c _). apply SINC2. unfold PM.vs_own. rewrite E. left. reflexivity. }
    split.
    { apply (PECFA.enc_keepA RSEGS EE L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB BRBc ov fb en2 (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC2| | exact EA2].
      - apply OUTO3. clear - Eop Eov; lia.
      - intros Hp. refine (OUTBc _ _ _). apply EINC2. unfold PEC.enc_own. replace (PEC.en_k en2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split.
    { apply (PMKA.u64_keepA RSEGS L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF2]. apply OUTO3. clear; lia. }
    split.
    { apply (PECFA.sink_keepA RSEGS L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB BRBc P osk k2 (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC2| | exact SKA2].
      - apply OUTO3. clear - Eop Eosk; lia.
      - intros Hp. refine (OUTBc _ _ _). apply KINC2. unfold PESK.sink_own. replace (PESK.sk_c k2 =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
    split.
    { change (PMSTA.base_okA RSEGS PMA.AD M4). apply (PMASK.base_keep L ar C LY LBc FF sp 22528 W3 M2 M4 EK24); [| exact BASE2]. intros a Ha. apply OUT3; clear - Ha O1; lia. }
    split.
    { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBc FF sp 22528 W3 M2 M4 EK24 e2 PECSA.addrs_wf_A); [| exact ERR2]. refine (SDEP W3 _). intros i N. apply OUT3; clear - N; lia. }
    split; [exact TBOK|].
    split.
    { apply (content_keepA' LBc FF sp 22528 W3 M2 M4 fb p s1 str sm op EK24 WAPP3 FRB BRBc (AOF ois 272 ltac:(lia) ltac:(lia))); [| exact SINC2| exact Iq2| | exact IA2| exact PA2| exact CONT2].
      - fold ois. apply OUTO3. clear - Eop Eois; lia.
      - intros q m Hq. exact (OUTBc q m Hq). }
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_stk w_more PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
      split; [reflexivity|]. split; [exact L2done|]. split; [exact L2depth|].
      split; [rewrite Lstk, HSTK; cbn [tl]; apply stk_conv_removelast|].
      split; [intros _ _; rewrite e_end_pos; unfold X1, w_depth; cbn [s_pos]; exact (Lpos MORE DONE)|].
      split; [exact L2estk|]. split; [exact L2edepth|]. split; [exact L2z| exact L2bad]. }
    split.
    { apply (PECFA.ec_state_keepA RSEGS AD L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB fb (s_ec (e_end X1)) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS2].
      fold oec. apply OUTO3. clear - Eop Eoec; lia. }
    split; [exact ECI2|].
    exact (PMKA.acc_keepA' L ar LBc FF sp 22528 W3 M2 M4 EK24 WAPP3 FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC2).
  -
    unfold PMSPA.src_step. cbn [PM.p_src]. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [intros X'; exact X'| clear; lia].
  - exact EIMP2.
  -
    apply (L5SAR.ahpres_of L ar LBX FF sp 22528 _ M M4).
    + apply (L5SAR.ek_trans L ar LBX FF sp 22528 _ M M1 M4).
      { exact (L5SAR.ek_W L ar LBX FF sp 22528 _ W1 M M1 (PMKA.ek_sublb L ar LB LBX FF sp 22528 W1 M M1 INCLx EK01) OW1). }
      apply (L5SAR.ek_trans L ar LBX FF sp 22528 _ M1 M2 M4).
      { apply (L5SAR.ek_callee L ar LBX (PM.parser_own s1) FF [] sp 22528 (sp - 32) 20480 _ (PEC.W_enc AD EE fb) M1 M2 HP2); [clear; lia| clear; lia|].
        intros a _ O. exact (OWE a O). }
      exact (L5SAR.ek_W L ar LBX FF sp 22528 _ W3 M2 M4 (PMKA.ek_sublb L ar LBc LBX FF sp 22528 W3 M2 M4 INCx EK24) OW3).
    + pose proof ASTK4 as (_ & _ & _ & _ & D4 & _). exact D4.
    + apply (L5SAR.dk_trans L ar LBX FF sp 22528 M M1 M4); [apply L5SAR.dk_grows; exact MGM1|].
      apply (L5SAR.dk_trans L ar LBX FF sp 22528 M1 M2 M4).
      { apply (L5SAR.dk_callee L ar LBX (PM.parser_own s1) FF [] sp 22528 (sp - 32) 20480 (PEC.W_enc AD EE fb) M1 M2 HP2); clear; lia. }
      exact (PMKA.dk_sublb L ar LBc LBX FF sp 22528 M2 M4 INCx DK24).
  -
    unfold PMSP.credit_keep, PECA.pot_allA, PECA.pot_encA, PEC.credit_add, PMSPA.scA in CK2 |- *. cbn [fst snd] in CK2 |- *.
    change (PM.pot_parser (PMSPA.HV L ar) (PM.PST 1 dn (dp - 1) src tb tg vb vk (removelast stk))) with (PM.pot_parser (PMSPA.HV L ar) s1).
    change (PM.pot_parser (PMSPA.HV L ar) (PM.PST mo dn dp src tb tg vb vk stk)) with (PM.pot_parser (PMSPA.HV L ar) s1). clear - CK2. lia.
  - exact (L5LZ.model_rt_trans model model1 model4 MRT1 (L5LZ.model_rt_trans model1 model2 model4 MRT2 (L5LZ.model_rt_trans model2 model3 model4 MRT3 MRT4))).
  - intros x Hx. apply INCLK2. apply INCLK4. exact Hx.
  - intros x Hx. apply INCAw4. apply INCAw2. exact Hx.
  - exact AM4.
  - change (ri_inv HI ((PM.sr_qc src, 16384) :: (vb, 32 * 2 ^ vk) :: (PM.vs_own tb ++ (PEC.enc_own en2 ++ PESK.sink_own k2)) ++ LBX) FF LK4 cr2 Aw4 M4 (vml_of model4)).
    exact (PMARS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH4).
Qed.

Theorem end_array_ok : PECSA.ann_shrink_spec L ar HI -> PECSA.v_end_arr_spec L ar HI P -> PECSA.end_array_spec L ar HI P.
Proof.
  intros ASH VEND. unfold PECSA.end_array_spec, PECSPA.end_array_spec. cbn [pa_end_array PeCLayoutA.CADDR_A].
  apply (end_core 0xb37a4 0xb381c 0xaae90 0x133608); [clear; lia| clear; lia| reflexivity| split; [clear; lia| reflexivity]| exact ea_runA| exact ea_runB| exact ASH|].
  unfold PECSA.v_end_arr_spec, PECSPA.v_end_arr_spec in VEND. cbn [pe_end_arr PeCLayoutA.EADDR_A] in VEND. exact VEND.
Qed.

Theorem end_object_ok : PECSA.ann_shrink_spec L ar HI -> PECSA.v_end_obj_spec L ar HI P -> PECSA.end_object_spec L ar HI P.
Proof.
  intros ASH VEND. unfold PECSA.end_object_spec, PECSPA.end_object_spec. cbn [pa_end_object PeCLayoutA.CADDR_A].
  apply (end_core 0xb5254 0xb52cc 0xabb0c 0x133640); [clear; lia| clear; lia| reflexivity| split; [clear; lia| reflexivity]| exact eo_runA| exact eo_runB| exact ASH|].
  unfold PECSA.v_end_obj_spec, PECSPA.v_end_obj_spec in VEND. cbn [pe_end_obj PeCLayoutA.EADDR_A] in VEND. exact VEND.
Qed.
End WithHeap.
End PEACEND.
