(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* [comment removed for export] *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require BvWfKernel.

From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_encoder.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PropExec CatExec CatSim SeqExec StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceAEx IcptIfaceA LibIface AxSymExec3 AxSymExec3Sound SegRun BigLinkBase BigLinkGlue L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreAS8 L5CoreSpecsAS8 L5StepARS8 L5CoreBRS8 L5ADetailHRS8.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PmLayout PmLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PmModel PmModelFacts PmStatics PmStaticsA PmSpecs PmSpecsA PmSpecsAX PeSpecsAa PnStatics PmCertKitG PmModelFactsA PmStep PeStepA PmParStep PmParKit PeASrcKit PeAParKit LibIfaceAB.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import PeCLayout PeCLayoutA.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8 Require Import PeCSink PeCModel PeCSpecs PeCFrame PeCSinkA PeCModelA PeCStaticsA PeCSpecsA PeCSpecsAa PeCFrameA PeCRdValD PeCGetLenW PeACReset1 PeASrcRead1 PmAUarK PmAUar PeAGlP1 PeAGlP2 PeAGlWP.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib Require Import Ea0_code_b6004_b6008 Ea0_code_b6370_b6374.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.Spec Require Import UbjRef.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.S8.Spec Require Import UbjRefFactsS8.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_encoder.lib.L5FastLia. Local Ltac lia := L5FastLia.plia.

Module PEACGL.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Abbreviation AD := PeCLayoutA.CADDR_A.
Abbreviation AAD := PeCLayoutA.CAADDR_A.
Abbreviation EE := PeCLayoutA.EADDR_A.

Lemma slice_pos_1 p pos : 0 <= pos < blen p -> UbjRef.slice p pos 1 = [bat p pos].
Proof.
  intros Hp. unfold UbjRef.slice, bat, blen in *. change (Z.to_nat 1) with 1%nat.
  remember (Z.to_nat pos) as n. assert (Hn : (n < length p)%nat) by lia. clear Heqn Hp.
  revert p Hn. induction n as [|n IH]; intros [|x p] Hn; cbn in Hn |- *; try lia; [reflexivity|]. apply IH. lia.
Qed.
Lemma bat_byte p pos : UbjRefFactsS8.bytes_ok p -> 0 <= pos < blen p -> 0 <= bat p pos < 256.
Proof.
  intros HB Hp. unfold bat, blen in *. apply (Forall_nth (fun b => 0 <= b < 256) p); [exact HB| lia].
Qed.
Lemma u8_at_inj M a b b' : L5.u8_at RSEGS M a b -> L5.u8_at RSEGS M a b' -> 0 <= b < 256 -> 0 <= b' < 256 -> b = b'.
Proof.
  intros U U' Hb Hb'. unfold L5.u8_at in U, U'. rewrite U in U'.
  apply (f_equal (fun o : option (list byte) => match o with Some (x :: _) => bv_unsigned x | _ => 0 end)) in U'. cbn beta iota in U'.
  rewrite !Z_to_bv_small in U' by (unfold bv_modulus; cbn; Lia.lia). exact U'.
Qed.
Lemma reg10_other (R : bvmap 5 word) v k : In k [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr (regupd R (reg 10) v) (reg k) = getr R (reg k).
Proof.
  intros Hk. assert (Hk' : k <> 10%nat /\ (k < 32)%nat) by (repeat (destruct Hk as [<-|Hk]; [split; lia|]); destruct Hk).
  apply PMPX.regupd_other_idx; lia.
Qed.
Lemma count_eq d kk : 0 <= d <= kk -> kk < 2 ^ 62 -> ((d - kk) mod 2 ^ 64) < 1 -> d = kk.
Proof.
  intros H1 H2 H3. destruct (Z.eq_dec d kk) as [E|N]; [exact E|]. exfalso.
  replace (d - kk) with ((d - kk + 2 ^ 64) + (-1) * 2 ^ 64) in H3 by lia. rewrite Z.mod_add in H3 by lia. rewrite Z.mod_small in H3 by lia. lia.
Qed.

Definition own (E : Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R (reg 1))) /\ L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R (reg 8)))
  /\ L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R (reg 9))) /\ L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R (reg 18)))
  /\ L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R (reg 19))) /\ L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R (reg 20)))
  /\ L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R (reg 21))) /\ L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R (reg 22)))
  /\ L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R (reg 23))) /\ L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R (reg 24)))
  /\ L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R (reg 25))) /\ L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R (reg 26))).
Definition ocell (E : Z) (a : Z) : Prop := E - 96 <= a < E.
Lemma own_agree E R M1 M1' : 0 <= E - 96 -> E <= 2 ^ 64 ->
  own E R M1 -> (forall a, ocell E a -> M1' (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)) -> own E R M1'.
Proof.
  intros H0 H1 (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11 & C12) AG. unfold own, ocell in *.
  repeat split; (eapply L5C.u64_at_agree; [ | | | eassumption]; [intros j Hj; apply AG; lia | lia | lia]).
Qed.

Definition zrun (pc0 : Z) : Prop :=
  forall (fx : FPState) (R R0 : bvmap 5 word) (M : word -> option byte) (E op oec F fl : Z),
  0 <= E < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= oec < 2 ^ 64 -> 0 <= F < 2 ^ 64 -> 0 <= fl < 2 ^ 64 ->
  0 <= (bv_unsigned (getr R0 (reg 1))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 8))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 9))) < 2 ^ 64 ->
  0 <= (bv_unsigned (getr R0 (reg 18))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 19))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 20))) < 2 ^ 64 ->
  0 <= (bv_unsigned (getr R0 (reg 21))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 22))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 23))) < 2 ^ 64 ->
  0 <= (bv_unsigned (getr R0 (reg 24))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 25))) < 2 ^ 64 -> 0 <= (bv_unsigned (getr R0 (reg 26))) < 2 ^ 64 ->
  getr R (reg 2) = Z_to_bv 64 (E - 128) -> getr R (reg 8) = Z_to_bv 64 E -> getr R (reg 9) = Z_to_bv 64 (E - 128) -> getr R (reg 18) = Z_to_bv 64 F ->
  getr R (reg 19) = Z_to_bv 64 op -> getr R (reg 20) = Z_to_bv 64 oec -> getr R (reg 21) = Z_to_bv 64 (op + 24) ->
  getr R (reg 24) = Z_to_bv 64 ((F / 8) + 2147450880) -> getr R (reg 25) = Z_to_bv 64 F -> getr R (reg 26) = Z_to_bv 64 2147450880 ->
  140735332487296 <= E <= 140737488355328 -> E mod 32 = 0 -> L5.writable RSEGS M (E - 128) 128 -> 6914048 <= op <= 140737488354944 ->
  op mod 8 = 0 -> (2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 3 ->
  L5KA.zeros_at M (((op + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M (((op + 20) / 8) + 2147450880) 1 -> L5.writable RSEGS M op 384 ->
  ((E - 128) + 128 <= op \/ op + 384 <= (E - 128)) -> 6914048 <= F <= 140737488355072 -> F mod 32 = 0 -> L5.defined M F 256 -> L5.writable RSEGS M F 256 ->
  (2147446784 + 17592186048512 <= F \/ F + 256 <= 2147446784) -> L5.writable RSEGS M ((F / 8) + 2147450880) 32 -> L5.u64_at RSEGS M (F + 248) fl ->
  4096 <= fl <= 140737488355327 -> L5.writable RSEGS M fl 1 -> (2147446784 + 17592186048512 <= fl \/ fl + 1 <= 2147446784) -> (F + 256 <= fl \/ fl + 1 <= F) ->
  ((E - 128) + 128 <= F \/ F + 256 <= (E - 128)) -> ((E - 128) + 128 <= fl \/ fl + 1 <= (E - 128)) -> (op + 384 <= F \/ F + 256 <= op) ->
  (op + 384 <= fl \/ fl + 1 <= op) -> (((op / 8) + 2147450880) + 48 <= ((F / 8) + 2147450880) \/ ((F / 8) + 2147450880) + 32 <= ((op / 8) + 2147450880)) ->
  L5.u64_at RSEGS M (E - 8) (bv_unsigned (getr R0 (reg 1))) -> L5.u64_at RSEGS M (E - 16) (bv_unsigned (getr R0 (reg 8))) ->
  L5.u64_at RSEGS M (E - 24) (bv_unsigned (getr R0 (reg 9))) -> L5.u64_at RSEGS M (E - 32) (bv_unsigned (getr R0 (reg 18))) ->
  L5.u64_at RSEGS M (E - 40) (bv_unsigned (getr R0 (reg 19))) -> L5.u64_at RSEGS M (E - 48) (bv_unsigned (getr R0 (reg 20))) ->
  L5.u64_at RSEGS M (E - 56) (bv_unsigned (getr R0 (reg 21))) -> L5.u64_at RSEGS M (E - 64) (bv_unsigned (getr R0 (reg 22))) ->
  L5.u64_at RSEGS M (E - 72) (bv_unsigned (getr R0 (reg 23))) -> L5.u64_at RSEGS M (E - 80) (bv_unsigned (getr R0 (reg 24))) ->
  L5.u64_at RSEGS M (E - 88) (bv_unsigned (getr R0 (reg 25))) -> L5.u64_at RSEGS M (E - 96) (bv_unsigned (getr R0 (reg 26))) ->
    exists fx' R' M', mem_grows M M'
    /\ (forall i, 0 <= i < 2 ^ 64 -> ~ (F <= i < F + 8) -> ~ (F / 8 + 2147450880 <= i < F / 8 + 2147450880 + 32) -> i <> fl -> ~ (op + 8 <= i < op + 9) ->
          M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
    /\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xb63c0) M' (seg_rom RSEGS))
    /\ (forall j, In j [3; 4; 27]%nat -> getr R' (reg j) = getr R (reg j))
    /\ (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R' (reg j) = getr R0 (reg j))
    /\ getr R' (reg 2) = Z_to_bv 64 E /\ L5.u8_at RSEGS M' fl 0 /\ L5.u8_at RSEGS M' (op + 8) 0.

Ltac zrun_tac Z_conc :=
  intros fx R R0 M E op oec F fl; intros;
  let P := fresh "P" in
  pose proof (Z_conc fx R M (fun j => match j with 2%nat => E | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl
        | 64%nat => bv_unsigned (getr R0 (reg 1)) | 65%nat => bv_unsigned (getr R0 (reg 8)) | 66%nat => bv_unsigned (getr R0 (reg 9))
        | 67%nat => bv_unsigned (getr R0 (reg 18)) | 68%nat => bv_unsigned (getr R0 (reg 19)) | 69%nat => bv_unsigned (getr R0 (reg 20))
        | 70%nat => bv_unsigned (getr R0 (reg 21)) | 71%nat => bv_unsigned (getr R0 (reg 22)) | 72%nat => bv_unsigned (getr R0 (reg 23))
        | 73%nat => bv_unsigned (getr R0 (reg 24)) | 74%nat => bv_unsigned (getr R0 (reg 25)) | 75%nat => bv_unsigned (getr R0 (reg 26)) | _ => 0 end)) as P;
  cbn beta iota in P;
  L5SAR.feed P ltac:(first [assumption | unfold PEAGLP2.aligned; assumption]);
  let fx' := fresh "fx'" in let R' := fresh "R'" in let M' := fresh "M'" in
  destruct P as (fx' & R' & M' & ?MG & _ & ?FRZ & ?MS & ?KS & ?E1 & ?E2 & ?E8 & ?E9 & _ & _ & ?E18 & ?E19 & ?E20 & ?E21 & ?E22 & ?E23 & ?E24 & ?E25 & ?E26 & ?FL0
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ?MO0 & _);
  exists fx', R', M';
  split; [assumption|];
  split; [intros i Hi N1 N2 N3 N4; match goal with FZ : forall i : Z, 0 <= i < 2 ^ 64 -> _ |- _ => apply FZ end;
          [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia| intros X; apply N4; lia]|];
  split; [assumption|];
  split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with KS0 : forall x, In x _ -> _ |- _ => apply KS0; inl end|]); destruct Hj|];
  split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr _ (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj|];
  split; [assumption|]; split; assumption.

Lemma zT_run : zrun 0xb60e4. Proof. unfold zrun. zrun_tac PEAGLP2.aglZTR_conc. Qed.
Lemma zi_run : zrun 0xb60b0. Proof. unfold zrun. zrun_tac PEAGLP2.aglZiR_conc. Qed.
Lemma zU_run : zrun 0xb6444. Proof. unfold zrun. zrun_tac PEAGLP2.aglZUR_conc. Qed.
Lemma zI_run : zrun 0xb6478. Proof. unfold zrun. zrun_tac PEAGLP2.aglZIR_conc. Qed.
Lemma zl_run : zrun 0xb63d4. Proof. unfold zrun. zrun_tac PEAGLP2.aglZlR_conc. Qed.
Lemma zL_run : zrun 0xb6410. Proof. unfold zrun. zrun_tac PEAGLP2.aglZLR_conc. Qed.
Lemma zD_run : zrun 0xb6274. Proof. unfold zrun. zrun_tac PEAGLP2.aglZDR_conc. Qed.

Lemma credit_le_keep p1 c1 c2 p2 : PMSP.credit_le p1 c1 -> PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_le p2 c2.
Proof. unfold PMSP.credit_le, PMSP.credit_keep. lia. Qed.
Lemma credit_keep_trans c1 c2 c3 p1 p2 p3 : PMSP.credit_keep c1 c2 p1 p2 -> PMSP.credit_keep c2 c3 p2 p3 -> PMSP.credit_keep c1 c3 p1 p3.
Proof. unfold PMSP.credit_keep. lia. Qed.

Lemma div8_off F a k : F / 8 * 8 = F -> F + 8 * k <= a < F + 8 * k + 8 -> a / 8 = F / 8 + k.
Proof. intros E H. symmetry. apply (Z.div_unique a 8 (F / 8 + k) (a - F - 8 * k)); lia. Qed.

Lemma frame_ok5_push FF fb f : PECA.frame_ok5 FF fb -> PECA.frame_ok5 (f :: FF) fb.
Proof. intros ((r0 & Hf) & Hm). split; [exists r0; right; exact Hf| exact Hm]. Qed.

Tactic Notation "wr_mem" integer(n) := unfold PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W; cbn [app]; do n right; left; reflexivity.
Ltac wr_rng := unfold L5.in_rng, PMSP.o_src, PMSP.o_p, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_v, PESK.o_sink;
  cbn [fst snd pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A].

Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface) (P : PESKA.sink_policyA).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Hypothesis PO : PESKA.sink_policyA_ok L P.
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

Hypothesis SRD : PECSA.src_read_spec L ar HI.
Hypothesis MKE : PECSA.make_ec_spec L ar HI.

Section Call.
Hypothesis PMODE : PESKA.spa_mode P.
Variables (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (model : Model) (K : TSet) (LBX : list (Z * Z)) (FF LK : list fframe) (Aw : list (Z * Z))
          (cr : credit) (sp r fb cat : Z) (p : list Z) (X : st) (s : PM.pst) (str : PM.vstr) (sm : PM.strm) (en : PEC.enc) (k : PESK.sink) (e : bool).
Hypothesis HH : ri_inv HI (PEC.owned s en k ++ LBX) FF LK cr Aw M (vml_of model).
Hypothesis AM : L5CA.amodel_ok Aw model.
Hypothesis K0 : K [].
Hypothesis ENT : PMSPA.entryA AD L ar R M sp r 5.
Hypothesis FRM : PMSPA.ffroomA 5 FF LK.
Hypothesis FRS : PMSPA.ffrsA FF sp.
Hypothesis FOK : PECA.frame_ok5 FF fb.
Hypothesis SP32 : sp mod 32 = 0.
Hypothesis A10 : getr R 10%bv = Z_to_bv 64 (PMSPA.o_p AD fb).
Hypothesis A11 : getr R 11%bv = Z_to_bv 64 (PMSPA.o_ec AD fb).
Hypothesis CPRE : PECA.crun_preA RSEGS AD AAD EE L ar P M fb p X s str sm en k e cat.
Hypothesis INCS : incl (PM.vs_own str) LBX.
Hypothesis POK : PECSPA.payload_ok p.
Hypothesis MP : PECSPA.mp_gl tt p X.
Hypothesis CRED : PMSP.credit_le (PECA.pot_allA L ar P s en k) cr.
Hypothesis KONT : forall (fx' : FPState) (R' : bvmap 5 word) (M' : word -> option byte) (model' : Model) (LK' : list fframe) (Aw' : list (Z * Z))
            (s' : PM.pst) (sm' : PM.strm) (e' : bool) (cr' : credit),
        regs_preserved R R' ->
        PECA.crun_preA RSEGS AD AAD EE L ar P M' fb p (PECSPA.gl_post p X) s' str sm' en k e' cat -> PECSPA.gl_ret p X R' ->
        PMSPA.src_step (PM.p_src s) (PM.p_src s') sm sm' -> (e = true -> e' = true) ->
        PM.p_tb s' = PM.p_tb s -> PM.p_tg s' = PM.p_tg s -> PM.p_b s' = PM.p_b s -> PM.p_k s' = PM.p_k s ->
        L5CA.ahpres L ar LBX FF sp (PMSPA.pm_scr 5) (PEC.W_crun AD EE fb) M M' ->
        PMSP.credit_keep cr cr' (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P s' en k) ->
        model_rt model model' -> incl LK' LK -> incl Aw Aw' -> L5CA.amodel_ok Aw' model' -> ri_inv HI (PEC.owned s' en k ++ LBX) FF LK' cr' Aw' M' (vml_of model') ->
        srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' r M' model') K.
Let op := PMSPA.o_p AD fb. Let ov := PMSPA.o_v AD fb. Let oec := PMSPA.o_ec AD fb. Let ois := PMSPA.o_is AD fb. Let osk := PESK.o_sink EE fb. Let otb := PMSPA.o_tb AD fb.
Let WR := PEC.W_crun AD EE fb.

Ltac entry_facts :=
  pose proof ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH); change (PMSPA.pm_scr 5) with 22528 in ASTK, STKSH; change (22528 / 8) with 2816 in STKSH;
  pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP); pose proof RAok as (Hr1 & Hr2);
  rewrite L5K.rl1 in Rra; rewrite L5K.rl2 in Rsp; rewrite L5K.rl3 in Rgp; rewrite L5K.rl4 in Rtp;
  pose proof FOK as ((rs & Hfb) & Fal);
  assert (Eop : op = fb + 592) by reflexivity; assert (Eov : ov = fb + 496) by reflexivity; assert (Eoec : oec = fb + 1120) by reflexivity;
  assert (Eois : ois = fb + 96) by reflexivity; assert (Eosk : osk = fb + 432) by reflexivity; assert (Eotb : otb = op + 336) by reflexivity;
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _);
  pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6); cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6; change (ff_bytes 5) with 2048 in F1, F2, F3, F4, F5, F6;
  unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, FS_BYTES in FSAPP; unfold FS_BYTES in FSCEIL, F1, F2;
  assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> PMSPA.aobjA FF a n)
    by (intros a' n' H1' H2'; exists (fb, 5, rs); split; [exact Hfb|]; cbn [ff_addr ff_class fst snd]; change (ff_bytes 5) with 2048; lia);
  assert (FB8 : forall j, (fb + 8 * j) mod 8 = 0)
    by (intros j'; pose proof (Z.div_mod fb 2048 ltac:(lia)) as E'; rewrite Fal, Z.add_0_r in E'; rewrite E';
        replace (2048 * (fb / 2048) + 8 * j') with ((256 * (fb / 2048) + j') * 8) by lia; apply Z_mod_mult);
  assert (O8 : op mod 8 = 0) by (rewrite Eop; replace (fb + 592) with (fb + 8 * 74) by lia; apply FB8);
  assert (Q8 : ov mod 8 = 0) by (rewrite Eov; replace (fb + 496) with (fb + 8 * 62) by lia; apply FB8);
  assert (I8 : ois mod 8 = 0) by (rewrite Eois; replace (fb + 96) with (fb + 8 * 12) by lia; apply FB8);
  assert (C8m : oec mod 8 = 0) by (rewrite Eoec; replace (fb + 1120) with (fb + 8 * 140) by lia; apply FB8);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 22528 HH (PMKA.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
    as ((O1 & O2 & O3 & O4 & O5) & OBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model ois 272 sp 22528 HH (PMKA.aobj_of_aobjA FF ois 272 (AOF ois 272 ltac:(lia) ltac:(lia)) I8) ltac:(lia) ltac:(reflexivity))
    as ((I1 & I2 & I3 & I4 & I5) & IBIG & _);
  pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model oec 16 sp 22528 HH (PMKA.aobj_of_aobjA FF oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) C8m) ltac:(lia) ltac:(reflexivity))
    as ((E1' & E2' & E3' & E4' & E5') & EBIG & _);
  assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMASK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH);
  assert (AOP : PMSPA.aobjA FF op 384) by (apply AOF; lia);
  assert (AOI : PMSPA.aobjA FF ois 272) by (apply AOF; lia).

Section Frame.
Variables (F fl : Z) (LK2 : list fframe) (M2 : word -> option byte) (model2 : Model).
Hypothesis G : PMAUK.gctx L ar HI LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k).
Hypothesis APART : forall a n sp0 scr0, (forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF sp0 scr0 (a + i)) -> 0 < n ->
  (a + n <= F \/ F + ff_bytes 2 <= a) /\ (a + n <= F / 8 + SB \/ F / 8 + SB + ff_bytes 2 / 8 <= a) /\ (a + n <= fl \/ fl + 1 <= a).
Let FF' := (F, 2, sp - 128 + 32) :: FF.

Ltac frame_facts :=
  pose proof G as G'; destruct G' as [_ GSPT GSLO GSHI _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS];
  change (ff_bytes 2) with 256 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF; unfold FS_BYTES in GFS2, GFLP.

Definition amid (fxi : FPState) (Ri : bvmap 5 word) (Mi : word -> option byte) (mdi : Model) (LKi : list fframe) (Awi : list (Z * Z)) (cri : credit)
           (si : PM.pst) (smi : PM.strm) (ei : bool) (Xi : st) : Prop :=
  (getr Ri (reg 2) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 8) = Z_to_bv 64 sp /\ getr Ri (reg 9) = Z_to_bv 64 (sp - 128) /\ getr Ri (reg 18) = Z_to_bv 64 F
   /\ getr Ri (reg 19) = Z_to_bv 64 op /\ getr Ri (reg 20) = Z_to_bv 64 oec /\ getr Ri (reg 21) = Z_to_bv 64 (op + 24) /\ getr Ri (reg 24) = Z_to_bv 64 (F / 8 + 2147450880)
   /\ getr Ri (reg 25) = Z_to_bv 64 F /\ getr Ri (reg 26) = Z_to_bv 64 2147450880 /\ (forall j, In j [3; 4; 27]%nat -> getr Ri (reg j) = getr R (reg j)))
  /\ PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PEC.owned si en k) Mi mdi LKi cri Awi
  /\ PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi en k ei cat
  /\ PMSPA.src_step (PM.p_src s) (PM.p_src si) sm smi /\ (e = true -> ei = true)
  /\ PMSP.credit_keep cr cri (PECA.pot_allA L ar P s en k) (PECA.pot_allA L ar P si en k)
  /\ (PM.p_tb si = PM.p_tb s /\ PM.p_tg si = PM.p_tg s /\ PM.p_b si = PM.p_b s /\ PM.p_k si = PM.p_k s).

Lemma cpre_keepA LB sp0 scr0 W Mi Mj Xi si smi ei :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKA.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  incl (PEC.owned si en k) LB -> incl (PM.vs_own str) LB ->
  (forall i, fb + 32 <= i < fb + 2040 -> L5.outside W i) -> (forall a, a < 6914048 -> L5.outside W a) ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi en k ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xi si str smi en k ei cat.
Proof.
  intros EK WAPP BRB OINC SINC OW OI OB CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own en) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own k) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> forall i, a <= i < a + n -> L5.outside W i) by (intros a n X1 X2 i Hi; apply OW; clear - X1 X2 Hi; lia).
  split.
  { apply (PMKA.parser_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB _ _ _ AOP); [exact PINC| apply OWo; clear - Eop; lia| | | | exact PA].
    - apply OB. apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity.
    - apply OB. apply PINC. unfold PM.parser_own, PM.vec_own. right. left. reflexivity.
    - intros c0 n0 p0 E0. apply OB. apply PINC. unfold PM.parser_own, PM.vs_own. rewrite E0. right. right. left. reflexivity. }
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB. apply SINC. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov; lia| exact EINC| | exact EA].
    intros Hp. apply OB. apply EINC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKA.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk; lia| exact KINC| | exact SKA].
    intros Hp. apply OB. apply KINC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [change (PMSTA.base_okA RSEGS PMA.AD Mj); apply (PMASK.base_keep L ar C LY LB FF sp0 scr0 W Mi Mj EK); [intros a Ha; apply OI; clear - Ha; lia| exact BASE]|].
  split.
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LB FF sp0 scr0 W Mi Mj EK ei PECSA.addrs_wf_A); [| exact ERR].
    intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OI. clear - DI; lia. }
  split; [exact TBOK|].
  split.
  { apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois; lia| exact SINC| | intros q m Hq; exact (OB q m Hq)| exact IA| exact PA| exact CONT].
    apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity. }
  split; [exact CL|].
  split; [apply (PECFA.ec_state_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB fb (s_ec Xi) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [fold oec; apply OWo; clear - Eoec; lia| exact ECS]|].
  split; [exact ECI|].
  exact (PMKA.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Lemma cpre_stepA LB sp0 scr0 W Mi Mj Xi si smi ei Xj sj ej :
  L5SAR.ek L ar LB FF sp0 scr0 W Mi Mj -> PMKA.wapp W ->
  (forall b, In b LB -> 0 <= fst b /\ fst b + snd b <= 2 ^ 47) ->
  incl (PEC.owned si en k) LB -> incl (PM.vs_own str) LB ->
  (forall i, fb + 32 <= i < fb + 2040 -> ~ (op <= i < op + 384) -> ~ (oec <= i < oec + 16) -> L5.outside W i) ->
  (forall q m, In (q, m) LB -> PMKA.blk_out W q m) ->
  PM.p_src sj = PM.p_src si -> PM.p_tb sj = PM.p_tb si -> PM.p_tg sj = PM.p_tg si ->
  PM.parser_at RSEGS AD PMSPA.accA PMSPA.annA Mj op ois sj -> PMSTA.base_okA RSEGS AD Mj -> PESTA.err_okA RSEGS AD AAD EE Mj ej ->
  PEC.clink p Xj sj smi en k -> PECA.ec_stateA RSEGS AD Mj fb (s_ec Xj) cat -> (s_ec Xj = true -> ej = true) ->
  PECA.crun_preA RSEGS AD AAD EE L ar P Mi fb p Xi si str smi en k ei cat -> PECA.crun_preA RSEGS AD AAD EE L ar P Mj fb p Xj sj str smi en k ej cat.
Proof.
  intros EK WAPP BRB OINC SINC OW OB ESRC ETB ETG PA' BASE' ERR' CL' ECS' ECI' CP. entry_facts.
  destruct CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  assert (PINC : incl (PM.parser_own si) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; left; exact Hx).
  assert (EINC : incl (PEC.enc_own en) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own k) LB) by (intros x Hx; apply OINC; unfold PEC.owned; apply in_or_app; right; apply in_or_app; right; exact Hx).
  assert (OWo : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op \/ op + 384 <= a) -> (a + n <= oec \/ oec + 16 <= a) -> forall i, a <= i < a + n -> L5.outside W i)
    by (intros a n X1 X2 X3 X4 i Hi; apply OW; clear - X1 X2 X3 X4 Hi; lia).
  split; [exact PA'|].
  split.
  { apply (PMKA.iss_keepA RSEGS AD L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ois str smi AOI); [exact SINC| apply OWo; clear - Eois Eop Eoec; lia| | exact IA].
    intros c0 n0 p0 E0. apply OB. apply SINC. unfold PM.vs_own. rewrite E0. left. reflexivity. }
  split.
  { apply (PECFA.enc_keepA RSEGS EE L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eov Eop Eoec; lia| exact EINC| | exact EA].
    intros Hp. apply OB. apply EINC. unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [apply (PMKA.u64_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eop Eoec; lia| exact VREF]|].
  split.
  { apply (PECFA.sink_keepA RSEGS L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB BRB P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [apply OWo; clear - Eosk Eop Eoec; lia| exact KINC| | exact SKA].
    intros Hp. apply OB. apply KINC. unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
  split; [exact BASE'|].
  split; [exact ERR'|].
  split; [rewrite ETB, ETG; exact TBOK|].
  split.
  { rewrite ESRC. apply (content_keepA' LB FF sp0 scr0 W Mi Mj fb p si str smi op EK WAPP FRB BRB AOI); [fold ois; apply OWo; clear - Eois Eop Eoec; lia| exact SINC| | intros q m Hq; exact (OB q m Hq)| exact IA| exact PA| exact CONT].
    apply PINC. unfold PM.parser_own, PM.src_own. left. reflexivity. }
  split; [exact CL'|]. split; [exact ECS'|]. split; [exact ECI'|].
  exact (PMKA.acc_keepA' L ar LB FF sp0 scr0 W Mi Mj EK WAPP FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) ACC).
Qed.

Ltac open_amid MID :=
  pose proof MID as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI & CP & ST & EIMP & CK & TBK);
  pose proof BI as (HHi & AMi & MRTi & INCAi & INCLi & ASTKi & EKbi & DKbi & OWNi & FSHDi);
  pose proof AMi as (Mhi & MIi).

Ltac vis_amid BI Hh Mv :=
  let X := fresh "VF" in
  pose proof (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k) G
                WR _ _ _ _ _ _ BI) as X;
  destruct X as ((WSi & ICi & CSBi & CUARi & _) & OWNv & (FDi & FWi & FSWi & FLCi & FLWi) & (FLCci & FLVi & VFi & VSi & VSHi));
  change (ff_bytes 2) with 256 in WSi, FDi, FWi, FSWi, FLCi, VFi, VSHi; change (256 / 8) with 32 in FSWi, VSHi;
  replace (sp - (sp - 128)) with 128 in WSi by (clear; lia); replace (F + 256 - 8) with (F + 248) in FLCi by (clear; lia);
  fold Hh in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi, FLVi, VFi, VSi, VSHi; fold Mv in WSi, ICi, CSBi, CUARi, OWNv, FDi, FWi, FSWi, FLCi, FLWi.

Lemma amid_regs fxi Ri Mi mdi LKi Awi cri si smi ei Y (fx' : FPState) R' md' :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei Y ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat -> getr R' (reg j) = getr Ri (reg j)) ->
  ri_inv HI (PEC.owned si en k ++ LBX) FF' LKi cri Awi Mi (vml_of md') -> L5CA.amodel_ok Awi md' -> model_rt mdi md' ->
  amid fx' R' Mi md' LKi Awi cri si smi ei Y.
Proof.
  intros MID RR HH' AM' MRT'. open_amid MID.
  split; [|split; [exact (PMAUK.binv_model L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PEC.owned si en k) Mi mdi LKi cri Awi md' BI HH' AM' MRT')| split; [exact CP| split; [exact ST| split; [exact EIMP| split; [exact CK| exact TBK]]]]]].
  split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
  split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
  split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 24%nat) by inl; exact J24|]. split; [rewrite (RR 25%nat) by inl; exact J25|].
  split; [rewrite (RR 26%nat) by inl; exact J26|].
  intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
Qed.

Lemma amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi ei Y (fxj : FPState) Rj (pci pcj : Z) Mjv (Wp : Z -> Prop) :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei Y ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fxj Rj (Z_to_bv 64 pcj) Mjv (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) Mjv ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ Wp a -> Mjv (Z_to_bv 64 a) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 a)) ->
  (forall a, Wp a -> F / 8 + SB <= a < F / 8 + SB + 32) ->
  (forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat -> getr Rj (reg j) = getr Ri (reg j)) ->
  (forall Mj mdj, mrestrict (ahid Awi mdi) Mj = Mjv -> ahid Awi mdj = ahid Awi mdi -> mem_grows Mi Mj ->
      amid fxj Rj Mj mdj LKi Awi cri si smi ei Y -> srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxj) RSEGS Rj pcj Mj mdj) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID MS MG FZ WPF RR KONT'. entry_facts. frame_facts. open_amid MID.
  set (LBi := PEC.owned si en k ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  unfold PMSPA.cfg.
  apply (L5SAR.apiece L ar C HI LYa HIok LBi FF' LKi cri Awi Mi mdi fxi fxj Ri pci Rj pcj Mjv Wp K HHi AMi MS MG FZ).
  { intros a Ha Wa. pose proof (WPF a Wa) as X'. split.
    - apply (L5SAR.fframe_shadow_client L ar LBi FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
      unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. unfold SB in X'. clear - X'; lia.
    - unfold SB in X'. pose proof GFR as (GF1 & _). assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia). clear - X' D1; lia. }
  intros Mj mdj HHj AMj MRTj HIDj VISj MGMj FRj VVj.
  assert (EKj : L5SAR.ek L ar LBi FF 0 0 [] Mi Mj).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mj _ [] (fun _ => False) G HHi); [intros a []|].
    intros a Ha Nw. apply FRj; [exact Ha|]. intros Wa. apply Nw. unfold PMAUK.WretX, PMAUK.Wret. left. left. right. change (ff_bytes 2 / 8) with 32. exact (WPF a Wa). }
  apply (KONT' Mj mdj VISj HIDj MGMj).
  split; [| split; [| split; [| split; [exact ST| split; [exact EIMP| split; [exact CK| exact TBK]]]]]].
  - split; [rewrite (RR 2%nat) by inl; exact J2|]. split; [rewrite (RR 8%nat) by inl; exact J8|]. split; [rewrite (RR 9%nat) by inl; exact J9|].
    split; [rewrite (RR 18%nat) by inl; exact J18|]. split; [rewrite (RR 19%nat) by inl; exact J19|]. split; [rewrite (RR 20%nat) by inl; exact J20|].
    split; [rewrite (RR 21%nat) by inl; exact J21|]. split; [rewrite (RR 24%nat) by inl; exact J24|]. split; [rewrite (RR 25%nat) by inl; exact J25|].
    split; [rewrite (RR 26%nat) by inl; exact J26|].
    intros j Hj. rewrite (RR j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (PMAUK.binv_piece L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k) G
             WR (PEC.owned si en k) Mi mdi LKi cri Awi Mj mdj Wp BI HHj AMj MRTj MGMj FRj).
    intros a Wa. right. right. change (ff_bytes 2 / 8) with 32. exact (WPF a Wa).
  - apply (cpre_keepA LBi 0 0 [] Mi Mj Y si smi ei EKj PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
Qed.

Lemma tail_Z pcz fxi Ri Mi mdi LKi Awi cri si smi ei Y :
  zrun pcz -> amid fxi Ri Mi mdi LKi Awi cri si smi ei Y -> s_ec Y = true -> PECRVD.but_pos (r_fail X) (w_more false Y) ->
  UbjRef.get_length p (s_pos X) = None ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri pcz Mi mdi) K.
Proof.
  intros ZR MID EY RV GLN. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 2, sp - 128 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR.
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 2) with 256 in ApF, ApSF. change (256 / 8) with 32 in ApSF. unfold SB in ApSF.
  assert (SHop : op / 8 + 2147450880 = fb / 8 + 2147450880 + 74).
  { rewrite Eop. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 592) with ((256 * (fb / 2048) + 74) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  destruct (APART (op / 8 + 2147450880) 48 0 0) as (_ & AsopSF & _).
  { intros i Hi'. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - SHop Hi'. lia. }
  { clear; lia. }
  change (256 / 8) with 32 in AsopSF. unfold SB in AsopSF.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  destruct (ZR fxi Ri R MVi sp op oec F fl) as (fx7 & R7 & M7v & MG7 & FRZ7 & MS7 & K347 & REG7 & E72 & FL0 & MO0);
    first [assumption | clear - GSLO GSHI GSPT; lia | clear - O1 O3; lia | clear - O1 O3 Eop Eoec; lia | clear - GFR; lia
          | clear - GL1 GL2; lia | clear - O2 GSLO; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | exact SP32 | exact O8 | exact GF32 | idtac].
  all: try (clear - ApF; lia). all: try (clear - ApFL; lia). all: try (clear - AsopSF; lia).
  assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb63c0 W_b6370 r F_b6370 eq_refl D_b6370 R7ra Hr1 Hr2) as MSr.
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k) G
           WR (PEC.owned si en k) Mi mdi LKi cri Awi (fun a => op + 8 <= a < op + 9) fxi fx7 Ri pcz R7 r M7v K BI).
  { intros a X'. split.
    - apply (L5SAR.fframe_client L ar (PEC.owned si en k ++ LBX) FF' 0 0 fb 5 rs); [right; exact Hfb| change (ff_bytes 5) with 2048; clear - X' Eop; lia].
    - intros O. apply (O (PMSP.o_p AD fb + 8, 8)); [unfold WR; wr_mem 0| wr_rng; clear - X' Eop; lia]. }
  { intros a. destruct (L5SAR.rng_dec a (op + 8) (op + 9)) as [X'|X']; [left; exact X'| right; exact X']. }
  { exact (msteps_trans _ _ _ _ MS7 MSr). }
  { exact MG7. }
  { intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 2) with 256 in Nw.
    apply FRZ7; [exact Ha| intros X'; apply Nw; left; left; left; clear - X'; lia| intros X'; apply Nw; left; left; right; unfold SB; clear - X'; lia
                | intros X'; apply Nw; left; right; clear - X'; lia| intros X'; apply Nw; right; clear - X'; lia]. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M7v) in VISf.
  set (LBi := PEC.owned si en k ++ LBX) in *.
  assert (EKf : L5SAR.ek L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf _ [(op + 8, 1)] (fun a => op + 8 <= a < op + 9) G HHi).
    - intros a X' O. apply (O (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X'; lia].
    - exact FZf. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (MO0f : L5.u8_at RSEGS Mf (op + 8) 0).
  { apply (proj1 (L5A.u8_at_vis Hi Mf (op + 8) 0 (OVIS (op + 8) 1 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - O1; lia) ltac:(clear - O1 O3; lia))). rewrite VISf. exact MO0. }
  assert (WAPP8 : PMKA.wapp [(op + 8, 1)]).
  { apply PMKA.wapp_cons; [| apply PMKA.wapp_nil]. cbn [fst snd]. unfold BIGSHADOW_LO, BIGSHADOW_HI. clear - OBIG; lia. }
  assert (OUT8 : forall a n, (a + n <= op + 8 \/ op + 9 <= a) -> forall i, a <= i < a + n -> L5.outside [(op + 8, 1)] i).
  { intros a n X3 i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr. clear - Hi' Hr X3. lia. }
  assert (OUTB8 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside [(op + 8, 1)] i).
  { intros q' m Hq i Hi' rr [<-|[]] Hr. unfold L5.in_rng in Hr. cbn [fst snd] in Hr.
    destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Hr Z'; lia. }
  assert (Iq : In (PM.sr_qc (PM.p_src si), PM.CHUNK) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
  assert (Ib : In (PM.p_b si, 32 * 2 ^ PM.p_k si) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vec_own; right; left; reflexivity).
  apply (KONT fx7 R7 Mf modelf LKi Awi (PMPK.set_more si 0) smi ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl | rewrite (K347 _) by inl; apply J34; inl ] |]).
    destruct Hj.
  - destruct (BRBi _ Iq) as (Xq1 & Xq2). destruct (BRBi _ Ib) as (Xb1 & Xb2). cbn [fst snd] in Xq1, Xq2, Xb1, Xb2. unfold PM.CHUNK in Xq2.
    unfold PECSPA.gl_post. rewrite GLN.
    apply (cpre_stepA LBi 0 0 [(op + 8, 1)] Mi Mf Y si smi ei (r_fail X) (PMPK.set_more si 0) ei EKf WAPP8 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' Ni _. apply (OUT8 i 1); clear - Hi' Ni; lia.
    + intros q' m Hq. exact (OUTB8 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMAPAR.parser_more_updA Mi Mf op ois si 0 PA).
      * clear - O1; lia.
      * clear - O1 O3; lia.
      * apply (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * apply (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (op + 9) 375 (AOF (op + 9) 375 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))). apply OUT8. clear; lia.
      * exact (PMKA.agsh_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB op 384 AOP).
      * pose proof PA as (_ & PDi & _). apply (L5.defined_grows Mi Mf _ _ MGf PDi).
      * exact MO0f.
      * left; reflexivity.
      * exact Xq1.
      * unfold PM.CHUNK. clear - Xq2; lia.
      * apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Iq). apply OUTB8. exact Iq.
      * exact Xb1.
      * clear - Xb2; lia.
      * apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ib). apply OUTB8. exact Ib.
      * intros c0 n0 p0 E0. assert (Ip : In (p0, c0) LBi) by (unfold LBi, PEC.owned; apply in_or_app; left; apply in_or_app; left; unfold PM.parser_own, PM.vs_own; rewrite E0; right; right; left; reflexivity).
        apply (PMKA.agA_blk L ar _ FF 0 0 _ Mi Mf EKf WAPP8 BRBi _ _ Ip). apply OUTB8. exact Ip.
    + change (PMSTA.base_okA RSEGS PMA.AD Mf). apply (PMASK.base_keep L ar C LY LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf); [| exact BASE]. intros a Ha. apply (OUT8 a 1); clear - Ha O1; lia.
    + apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF 0 0 [(op + 8, 1)] Mi Mf EKf ei PECSA.addrs_wf_A); [| exact ERR].
      intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
      split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply (OUT8 a 1); clear - DI O1; lia.
    + apply (PECRVD.clink_but_pos p (r_fail X) (w_more false Y)); [reflexivity| exact RV|].
      destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
      unfold PEC.clink, PMPK.set_more. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_more PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src PEC.b2z].
      split; [reflexivity|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
      split; [intros X' _; discriminate X'|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad].
    + change (s_ec (r_fail X)) with true.
      pose proof ECS as ECS0. unfold PECA.ec_stateA in ECS0 |- *. rewrite EY in ECS0. fold oec in ECS0 |- *. destruct ECS0 as (v & Hv & ECv).
      exists v. split; [exact Hv|].
      pose proof ECv as (ECa & ECb & ECc & ECd). split; [|split; [|split]].
      * apply (PMF.u32_at_agree RSEGS Mi Mf); [| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECa].
        apply (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB oec 4 (AOF oec 4 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
      * apply (L5C.u64_at_agree RSEGS Mi Mf); [| clear - O1 Eop Eoec; lia| clear - O3 Eop Eoec; lia| exact ECb].
        apply (proj1 (PMKA.agA_obj L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB (oec + 8) 8 (AOF (oec + 8) 8 ltac:(lia) ltac:(lia)) ltac:(apply OUT8; clear - Eop Eoec; lia))).
      * apply (L5.defined_grows Mi Mf _ _ MGf ECc).
      * exact (PMKA.acc_keepA' L ar _ FF 0 0 _ Mi Mf EKf WAPP8 FRB oec 16 (AOF oec 16 ltac:(lia) ltac:(lia)) ECd).
    + intros _. apply ECI. exact EY.
    + exact CP.
  - unfold PECSPA.gl_ret. rewrite GLN. exact I.
  - unfold PMPK.set_more. cbn [PM.p_src]. exact ST.
  - exact EIMP.
  - unfold PMPK.set_more. cbn [PM.p_tb]. exact (proj1 TBK).
  - unfold PMPK.set_more. cbn [PM.p_tg]. exact (proj1 (proj2 TBK)).
  - unfold PMPK.set_more. cbn [PM.p_b]. exact (proj1 (proj2 (proj2 TBK))).
  - unfold PMPK.set_more. cbn [PM.p_k]. exact (proj2 (proj2 (proj2 TBK))).
  - exact AHf.
  - unfold PMSP.credit_keep, PMPK.set_more, PECA.pot_allA, PEC.credit_add, PM.pot_parser in CK |- *. cbn [PM.p_k PM.p_tb PM.p_tg fst snd] in CK |- *. exact CK.
  - exact MRTf.
  - exact INCLi.
  - exact INCAi.
  - exact AMf.
  - unfold PMPK.set_more. change (PEC.owned (PM.PST 0 (PM.p_done si) (PM.p_depth si) (PM.p_src si) (PM.p_tb si) (PM.p_tg si) (PM.p_b si) (PM.p_k si) (PM.p_stk si)) en k)
      with (PEC.owned si en k). exact HHf.
Qed.

Lemma call_mkec (q v : Z) fxi Ri Mi mdi LKi Awi cri si smi ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei Y ->
  getr Ri (reg 1) = Z_to_bv 64 q -> L5.ra_ok q -> getr Ri (reg 10) = Z_to_bv 64 oec -> getr Ri (reg 11) = Z_to_bv 64 v -> 1 <= v <= 64 ->
  (forall fx' R' M' md' LK' Aw', regs_preserved Ri R' -> amid fx' R' M' md' LK' Aw' cri si smi true (w_ec true Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg RSEGS R' q M' md') K) ->
  srealizes RSEGS SCFG (PMSPA.cfg RSEGS Ri 0xae310 Mi mdi) K.
Proof.
  intros MID J1 RAq J10 J11 Hv KONT'. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (LBi := PEC.owned si en k ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  assert (ECD : L5.defined Mi oec 16 /\ PMSPA.accA Mi oec 16).
  { pose proof ECS as ECS0. unfold PECA.ec_stateA in ECS0. fold oec in ECS0.
    destruct (s_ec Y); [destruct ECS0 as (v0 & _ & (_ & _ & D' & A')); exact (conj D' A')| destruct ECS0 as (_ & _ & D' & A'); exact (conj D' A')]. }
  assert (SZK : forall Mc lo g, L5SAR.ek L ar LBX FF sp 22528 WR M Mc -> sp - 22528 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g).
  { intros Mc lo g EKc H1' H2' H3' H4'.
    assert (WAPPR : PMKA.wapp WR).
    { intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
      pose proof FSAPP as (FA0 & FA1 & FA2).
      unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
      cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin.
      repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin. }
    apply (PMKA.stksh_keepA L ar LBX FF sp 22528 WR M Mc EKc WAPPR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
    apply (PMKA.shadow_zero_sub M (sp - 22528) 2816); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
    apply PMKA.mod16_8'. replace (sp - 22528) with (sp + (-1408) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  unfold PECSA.make_ec_spec, PECSPA.make_ec_spec in MKE.
  apply (MKE fxi Ri Mi mdi K LBi FF' LKi Awi cri oec v (sp - 128) q ei HHi AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 1) with 14336. change (14336 / 8) with 1792.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 22528 128 14336 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply SZK; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 14336) with (sp + (-904) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDFi & _).
    apply (PMAUAR.ffroomA_push 5 1 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 2 (sp - 128 + 32) FRS); clear; lia. }
  { rewrite L5K.rl10. exact J10. }
  { rewrite L5K.rl11. exact J11. }
  { exact Hv. }
  { apply PMAUAR.aobjA_push. apply AOF; clear - Eoec; lia. }
  { exact C8m. }
  { exact (proj1 ECD). }
  { exact (proj2 ECD). }
  { exact BASE. }
  { exact ERR. }
  intros fx6 R6 M6 model6 LK6 Aw6 RP6 EC6 ERR6 HP6 MRT6 INCLK6 INCAw6 AM6 HH6.
  change (PMSPA.pm_scr 1) with 14336 in HP6.
  set (Wc6 := (oec, 16) :: (if ei then [] else PMSPA.err_W AD)) in HP6.
  assert (Wc6R : forall rr a, In rr Wc6 -> L5.in_rng rr a -> (oec <= a < oec + 16) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [left; exact Hr|]. right. destruct ei; [destruct Hin|].
    unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
    destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia. }
  assert (BI6 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PEC.owned si en k) M6 model6 LK6 cri Aw6).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si en k) (PEC.owned si en k) (PEC.owned si en k) Mi mdi LKi cri Awi M6 model6 LK6 cri Aw6 14336 Wc6 BI HP6 HH6 AM6 MRT6 INCAw6 INCLK6);
      [clear; lia| clear; lia| | | intros a X'; exact X'].
    - intros rr a Hin Hr. change (ff_bytes 2 / 8) with 32. unfold ocell, SB.
      pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
      assert (DF2 : F / 8 <= 17592186044384) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      pose proof FSAPP as (FA0 & FA1 & FA2).
      destruct (Wc6R rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT Eop Eoec F2 FSCEIL; lia|]).
      + destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2 Eoec; lia.
      + clear - X' DF1; lia.
    - intros a Hc Ho rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [X'|X'].
      + apply (Ho (PMSP.o_ec AD fb, 16)); [unfold WR; wr_mem 6| wr_rng; clear - X' Eoec; lia].
      + unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr X' Eoec O1 Eop; lia|].
        destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin.
        destruct Hin as [<-|[<-|[]]].
        * apply (Ho (pa_errcat_guard AD, 2)); [unfold WR; wr_mem 7| exact Hr].
        * apply (Ho (pa_atexit AD, 544)); [unfold WR; wr_mem 8| exact Hr]. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 2, sp - 128 + 32)] sp 22528 (sp - 128) 14336 Wc6 Wc6 Mi M6 ltac:(rewrite app_nil_l; exact HP6) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK6.
  assert (WAPP6 : PMKA.wapp Wc6).
  { intros rr Hin. unfold Wc6 in Hin. unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|Hin]; cbn [fst snd].
    - pose proof FSAPP as (FA0 & FA1 & FA2). destruct FA1 as [Y'|Y']; clear - Y' F1 F2 Eoec; lia.
    - destruct ei; [destruct Hin|]. unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. destruct Hin as [<-|[<-|[]]]; cbn [fst snd]; clear; lia. }
  assert (OUTB6 : forall q' m, In (q', m) LBi -> forall i, q' <= i < q' + m -> L5.outside Wc6 i).
  { intros q' m Hq i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y'].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m oec 16 HHi Hq (PMAUAR.aobjA_push FF oec 16 _ (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia)))) as [Z'|Z']; clear - Hi' Y' Z'; lia.
    - pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ q' m HHi Hq) as Z'. destruct Z' as [Z'|Z']; clear - Hi' Y' Z'; lia. }
  apply (KONT' fx6 R6 M6 model6 LK6 Aw6 RP6).
  split; [|split; [exact BI6| split; [| split; [exact ST| split; [intros _; reflexivity| split; [exact CK| exact TBK]]]]]].
  - pose proof (fun j Hj => L5SAR.cs_of_preserved Ri R6 j RP6 Hj) as R6c.
    split; [rewrite (R6c 2%nat) by inl; exact J2|]. split; [rewrite (R6c 8%nat) by inl; exact J8|]. split; [rewrite (R6c 9%nat) by inl; exact J9|].
    split; [rewrite (R6c 18%nat) by inl; exact J18|]. split; [rewrite (R6c 19%nat) by inl; exact J19|]. split; [rewrite (R6c 20%nat) by inl; exact J20|].
    split; [rewrite (R6c 21%nat) by inl; exact J21|]. split; [rewrite (R6c 24%nat) by inl; exact J24|]. split; [rewrite (R6c 25%nat) by inl; exact J25|].
    split; [rewrite (R6c 26%nat) by inl; exact J26|].
    intros j Hj. rewrite (R6c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  - apply (cpre_stepA LBi sp 22528 Wc6 Mi M6 Y si smi ei (w_ec true Y) si true EK6 WAPP6 BRBi).
    + unfold LBi. apply incl_appl. apply incl_refl.
    + unfold LBi. apply incl_appr. exact INCS.
    + intros i Hi' N1 N2 rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - N2 Y'; lia| clear - Hi' Y' Eop O1; lia].
    + intros q' m Hq. exact (OUTB6 q' m Hq).
    + reflexivity. + reflexivity. + reflexivity.
    + apply (PMKA.parser_keepA RSEGS AD L ar LBi FF sp 22528 Wc6 Mi M6 EK6 WAPP6 FRB BRBi _ _ _ AOP); [| | | | | exact PA].
      * unfold LBi, PEC.owned. intros x Hx. apply in_or_app. left. apply in_or_app. left. exact Hx.
      * intros i Hi' rr Hin Hr. destruct (Wc6R rr i Hin Hr) as [Y'|Y']; [clear - Hi' Y' Eop Eoec; lia| clear - Hi' Y' Eop O1; lia].
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.src_own; left; reflexivity.
      * unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vec_own. right; left; reflexivity.
      * intros c0 n0 p0 E0. unfold PMKA.blk_out. apply OUTB6. unfold LBi, PEC.owned. apply in_or_app; left. apply in_or_app; left. unfold PM.parser_own, PM.vs_own. rewrite E0. right; right; left; reflexivity.
    + apply (PMAPAR.base_keepW L ar C LY LBi FF sp 22528 Wc6 Mi M6 EK6); [| | | | exact BASE].
      * intros a Ha rr Hin Hr. destruct (Wc6R rr a Hin Hr) as [Y'|Y']; [clear - Ha Y' Eoec Eop O1; lia| clear - Ha Y'; lia].
      * intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
      * intros rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr; lia.
      * intros a Ha rr Hin Hr. unfold Wc6 in Hin. destruct Hin as [<-|Hin]; [unfold L5.in_rng in Hr; cbn [fst snd] in Hr; clear - Hr Ha Eoec Eop O1; lia|]. destruct ei; [destruct Hin|].
        unfold PMSPA.err_W in Hin. cbn [pa_errcat_guard pa_atexit AD PeCLayoutA.CADDR_A] in Hin. unfold L5.in_rng in Hr.
        destruct Hin as [<-|[<-|[]]]; cbn [fst snd] in Hr; clear - Hr Ha; lia.
    + exact ERR6.
    + destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
      unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad s_ec w_ec].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|]. split; [exact Lpos|]. split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad].
    + unfold PECA.ec_stateA. cbn [s_ec w_ec]. fold oec. exists v. split; [exact Hv| exact EC6].
    + intros _; reflexivity.
    + exact CP.
Qed.

Lemma wr_wav : forall rr a, In rr WR -> L5.in_rng rr a -> ~ ocell sp a /\ ~ (F / 8 + SB <= a < F / 8 + SB + ff_bytes 2 / 8).
Proof.
  entry_facts. frame_facts.
  assert (WRR' : forall rr a, In rr WR -> L5.in_rng rr a -> (fb + 32 <= a < fb + 2040) \/ (0x674080 <= a < 0x695df4)).
  { intros rr a Hin Hr. unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
    cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin. unfold L5.in_rng in Hr.
    repeat (destruct Hin as [<-|Hin]; [cbn [fst snd] in Hr; clear - Hr; lia|]). destruct Hin. }
  intros rr a Hin Hr. change (ff_bytes 2 / 8) with 32. unfold ocell, SB.
  pose proof GFR as (GF1 & GF2 & _). assert (DF1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
  assert (DF2 : F / 8 <= 17592186044384) by (apply Z.div_le_upper_bound; clear - GF2; lia).
  pose proof FSAPP as (FA0 & FA1 & FA2).
  destruct (WRR' rr a Hin Hr) as [X'|X']; (split; [clear - X' SLO SPT F2 FSCEIL; lia|]).
  - destruct FA1 as [Y'|Y']; clear - X' Y' DF1 DF2 F1 F2; lia.
  - clear - X' DF1; lia.
Qed.

Lemma wappR : PMKA.wapp WR.
Proof.
  entry_facts. intros rr Hin. destruct rr as [ra' rn]. unfold BIGSHADOW_LO, BIGSHADOW_HI. cbn [fst snd].
  pose proof FSAPP as (FA0 & FA1 & FA2).
  unfold WR, PEC.W_crun, PMSP.W_run, PMSP.W_srcf, PMSP.err_W, PMSP.o_src, PMSP.o_is, PMSP.o_tb, PMSP.o_vec, PMSP.o_ec, PMSP.o_p, PMSP.o_v, PESK.o_sink in Hin.
  cbn [app pa_off_p pa_off_is pa_off_ec pa_off_v pe_off_sink pa_errcat_guard pa_atexit AD EE PeCLayoutA.CADDR_A PeCLayoutA.EADDR_A] in Hin.
  repeat (destruct Hin as [Hin|Hin]; [injection Hin; intros <- <-; destruct FA1 as [FA1|FA1]; clear - FA0 FA1 FA2 F1 F2; lia|]). destruct Hin.
Qed.

Lemma szk Mc lo g : L5SAR.ek L ar LBX FF sp 22528 WR M Mc -> sp - 22528 <= lo -> lo + 8 * g <= sp -> lo mod 8 = 0 -> 0 <= g -> shadow_zero Mc lo g.
Proof.
  entry_facts. intros EKc H1' H2' H3' H4'.
  apply (PMKA.stksh_keepA L ar LBX FF sp 22528 WR M Mc EKc wappR lo g); [clear - H1' SLO SPT; lia| clear - H1' SLO; lia| clear - H2' SHI SPT; lia| exact H3'| exact H4'|].
  apply (PMKA.shadow_zero_sub M (sp - 22528) 2816); [| exact H3'| exact H1'| clear - H2'; lia| exact H4'| exact STKSH].
  apply PMKA.mod16_8'. replace (sp - 22528) with (sp + (-1408) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16.
Qed.

Lemma call_read (q kk ra g sv : Z) fxi Ri Mi mdi LKi Awi cri si smi ei Y :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei Y -> s_more Y = true -> s_done Y = false -> 0 <= s_pos Y <= blen p ->
  getr Ri (reg 1) = Z_to_bv 64 ra -> L5.ra_ok ra ->
  getr Ri (reg 10) = Z_to_bv 64 (op + 24) -> getr Ri (reg 11) = Z_to_bv 64 q -> getr Ri (reg 12) = Z_to_bv 64 kk ->
  q = F + 8 * g -> 4 <= g <= 30 -> 1 <= kk <= 8 ->
  L5.u8_at RSEGS (mrestrict (ahid Awi mdi) Mi) (F / 8 + 2147450880 + g) sv -> (sv = 0 \/ kk <= sv <= 7) ->
  (forall (fx2 : FPState) R2 M2 md2 LK2' Aw2 src2 smi2 d, regs_preserved Ri R2 -> getr R2 (reg 10) = Z_to_bv 64 d -> 0 <= d <= kk ->
      (d < kk -> s_pos Y + d = blen p) -> s_pos Y + d <= blen p ->
      L5.bytes_at RSEGS M2 q (UbjRef.slice p (s_pos Y) d) ->
      amid fx2 R2 M2 md2 LK2' Aw2 cri (PMSPA.with_src si src2) smi2 ei (w_pos (s_pos Y + d) Y) ->
      srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx2) RSEGS R2 ra M2 md2) K) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri (pa_src_read AD) Mi mdi) K.
Proof.
  intros MID MORE DONE PPOS J1 RAq J10 J11 J12 Eq Hg Hkk SHB SVK KX. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  set (LBi := PEC.owned si en k ++ LBX) in *.
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HHi) as (WBi & _ & _ & _ & _ & _ & _ & _ & _ & _ & NDi & NDFi & _).
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 2, sp - 128 + 32) FOK).
  assert (PINC : incl (PM.parser_own si) LBi) by (unfold LBi, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; left; exact Hx).
  assert (SINC : incl (PM.vs_own str) LBi) by (unfold LBi; apply incl_appr; exact INCS).
  assert (EINC : incl (PEC.enc_own en) LBi) by (unfold LBi, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; left; exact Hx).
  assert (KINC : incl (PESK.sink_own k) LBi) by (unfold LBi, PEC.owned; intros x Hx; apply in_or_app; left; apply in_or_app; right; apply in_or_app; right; exact Hx).
  set (qc := PM.sr_qc (PM.p_src si)) in *.
  assert (Iq : In (qc, 16384) LBi) by (apply PINC; unfold PM.parser_own, PM.src_own; left; reflexivity).
  destruct (BRBi _ Iq) as (Bq0' & Bq47). cbn [fst snd] in Bq0', Bq47.
  pose proof (WBi _ Iq) as ((Bq0 & Bq1 & Bq2 & Bq3 & Bq4 & Bq5) & _). cbn [fst snd] in Bq0, Bq1, Bq2, Bq3, Bq4, Bq5. unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI, PM.CHUNK in Bq5, Bq4.
  destruct Bq5 as (_ & Bq5 & _).
  pose proof (PMASK.blk_img L ar C HI LY HIok _ _ _ _ _ _ _ _ _ HHi Iq) as Bqi. unfold PM.CHUNK in Bqi.
  assert (EPO : LBi = PM.parser_own si ++ (PEC.enc_own en ++ PESK.sink_own k ++ LBX)) by (unfold LBi, PEC.owned; rewrite <- !app_assoc; reflexivity).
  assert (NDL : NoDup (map fst (PM.parser_own si ++ (PEC.enc_own en ++ PESK.sink_own k ++ LBX)))) by (rewrite <- EPO; exact NDi).
  assert (NEQ : forall q' m, In (q', m) (PEC.enc_own en ++ PESK.sink_own k ++ LBX) -> q' <> qc).
  { intros q' m Hin. apply not_eq_sym. apply (PMPK.fst_neq_app (PM.parser_own si) (PEC.enc_own en ++ PESK.sink_own k ++ LBX) qc 16384 q' m NDL); [| exact Hin].
    unfold PM.parser_own, PM.src_own. left. reflexivity. }

  assert (CLfb : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> 0 < n -> forall i, 0 <= i < n -> aclient L ar (PEC.owned s en k ++ LBX) FF 0 0 (a + i)).
  { intros a n X1 X2 X3 i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. split; [clear - X1 X2 Hi'; lia| intros Y'; clear - X1 X2 Hi' Y'; lia]. }
  destruct (APART op 384 0 0 (CLfb op 384 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (ApF & ApSF & ApFL).
  destruct (APART ois 272 0 0 (CLfb ois 272 ltac:(clear - Eois; lia) ltac:(clear - Eois; lia) ltac:(clear; lia)) ltac:(clear; lia)) as (AiF & AiSF & AiFL).
  change (ff_bytes 2) with 256 in ApF, ApSF, AiF, AiSF. change (256 / 8) with 32 in ApSF, AiSF.
  pose proof GFR as (GF1 & GF2 & _).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia).

  assert (FDm : L5.defined Mi F 256) by (apply (proj1 (L5A.defined_vis Hi Mi F 256 VFi)); exact FDi).
  assert (SHBm : L5.u8_at RSEGS Mi (F / 8 + 2147450880 + g) sv).
  { apply (proj1 (L5A.u8_at_vis Hi Mi (F / 8 + 2147450880 + g) sv (L5A.avis_sub Hi (F / 8 + SB) 32 (F / 8 + 2147450880 + g) 1 VSHi ltac:(unfold SB; clear - Hg; lia) ltac:(unfold SB; clear - Hg; lia))
             ltac:(clear - GF1 Hg; lia) ltac:(unfold SB; clear - GF1 GF2 Hg; lia))). exact SHB. }
  assert (ACCq : PMSPA.accA Mi q kk).
  { unfold PMSPA.accA, aacc. intros a Ha. unfold S.
    assert (Da : a / 8 + SB = F / 8 + 2147450880 + g) by (unfold SB; rewrite (div8_off F a g (proj1 GF8)); [clear; lia| clear - Ha Eq Hkk; lia]).
    rewrite Da. pose proof (L5ADHR.byte_of_u8 Mi _ sv SHBm ltac:(right; clear - GF1 Hg; lia) ltac:(clear - GF1 GF2 Hg; lia)) as BY.
    destruct SVK as [S0|Skk]; [left; rewrite <- S0; exact BY| right]. exists sv. split; [exact BY|]. split; [clear - Skk Hkk; lia|].
    assert (Am : a mod 8 = a - q) by (rewrite Eq; rewrite (Zmod_eq a 8) by (clear; lia); rewrite (div8_off F a g (proj1 GF8)) by (clear - Ha Eq Hkk; lia); clear - GF8; lia).
    rewrite Am. clear - Ha Skk; lia. }
  destruct CL as (Lmore & Ldone & Ldepth & Lstk & Lpos & Lestk & Ledepth & Lz & Lbad).
  pose proof (Lpos MORE DONE) as POS.

  unfold PECSA.src_read_spec, PECSPA.src_read_spec, PECSPA.csrc_spec in SRD.
  apply (SRD fxi Ri Mi mdi K (PEC.enc_own en ++ PESK.sink_own k ++ LBX) FF' LKi Awi cri (sp - 128) ra fb p si str smi [(q, kk)] ltac:(rewrite <- EPO; exact HHi) AMi K0).
  { split; [rewrite L5K.rl1; exact J1|]. split; [exact RAq|]. split; [rewrite L5K.rl2; exact J2|].
    split; [rewrite L5K.rl3; rewrite (J34 3%nat) by inl; rewrite <- L5K.rl3; exact Rgp|].
    split; [rewrite L5K.rl4; rewrite (J34 4%nat) by inl; rewrite <- L5K.rl4; exact Rtp|].
    change (PMSPA.pm_scr 4) with 20480. change (20480 / 8) with 2560.
    split; [apply (L5SAR.astk_sub ar Mi Mi sp 22528 128 20480 ASTKi (mem_grows_refl Mi)); [clear; lia| clear; lia| clear; lia| replace (sp - 128) with (sp + (-8) * 16) by (clear; lia); rewrite Z_mod_plus_full; exact A16]|].
    apply szk; [exact EKbi| clear; lia| clear; lia| | clear; lia].
    apply PMKA.mod16_8'. replace (sp - 128 - 20480) with (sp + (-1288) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { apply (PMAUAR.ffroomA_push 5 4 FF LK LKi _ FRM INCLi); [exact NDFi| clear; lia]. }
  { apply (PMAUAR.ffrsA_push FF sp (sp - 128) F 2 (sp - 128 + 32) FRS); clear; lia. }
  { exact FOK'. }
  { replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { unfold PMSPA.o_src. fold op. rewrite L5K.rl10. exact J10. }
  { exists q, kk. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [exact Hkk|].
    split; [exists (F, 2, sp - 128 + 32); split; [left; reflexivity| cbn [ff_addr ff_class fst snd]; change (ff_bytes 2) with 256; clear - Eq Hg Hkk; lia]|].
    split; [apply (L5.defined_sub Mi F 256); [exact FDm| clear - Eq Hg; lia| clear - Eq Hg Hkk; lia]|].
    split; [exact ACCq|]. split; [fold ois; clear - AiF Eq Hg Hkk; lia| fold op; unfold PECA.RDR_BYTES; clear - ApF Eq Hg Hkk; lia]. }
  { exists q, kk. split; [rewrite L5K.rl11; exact J11|]. split; [rewrite L5K.rl12; exact J12|]. split; [clear - Q0f GF2 Eq Hg Hkk; lia|]. split; [clear - Hkk; lia| reflexivity]. }
  { exact PA. }
  { exact IA. }
  { exact BASE. }
  { exact ACC. }
  { intros x Hx. apply in_or_app. right. apply in_or_app. right. exact (INCS x Hx). }
  { exact POK. }
  { exact CONT. }
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 RP4 PA4 IA4 STEP4 RES4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
  change (PMSPA.pm_scr 4) with 20480 in HP4. rewrite <- EPO in HP4, HH4.
  set (Wc := PMSPA.W_src AD fb (PM.p_src si) ++ [(q, kk)]) in HP4.
  assert (WcR : forall rr a, In rr Wc -> L5.in_rng rr a ->
            (op + 280 <= a < op + 320) \/ (ois + 40 <= a < ois + 48) \/ (ois + 152 <= a < ois + 156) \/ (qc <= a < qc + 16384) \/ (q <= a < q + kk)).
  { intros rr a Hin Hr. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin.
    unfold L5.in_rng in Hr. fold qc in Hin. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd] in Hr; unfold PM.CHUNK in Hr; clear - Hr Eop Eois;
      [left|right;left|right;right;left|right;right;right;left|right;right;right;right]; lia. }
  assert (BI4 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PEC.owned si en k) M4 md4 LK4 cri Aw4).
  { apply (PMAUK.binv_callee L ar C HI HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k) G
             WR WR (PEC.owned si en k) (PEC.owned si en k) (PEC.owned si en k) Mi mdi LKi cri Awi M4 md4 LK4 cri Aw4 20480 Wc BI HP4 HH4 AM4 MRT4 INCAw4 INCLK4);
      [clear; lia| clear; lia| | | intros a X'; exact X'].
    - intros rr a Hin Hr. change (ff_bytes 2 / 8) with 32. unfold ocell, SB.
      assert (D1 : 0 <= F / 8) by (apply Z.div_pos; clear - GF1; lia).
      assert (D2 : F / 8 <= 17592186044384) by (apply Z.div_le_upper_bound; clear - GF2; lia).
      destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|X']]]]; (split; [clear - X' O2 I2 Bq4 GFCEIL GSLO Eop Eois GF2 Eq Hg Hkk; lia|]).
      + clear - X' OBIG D1 D2; lia.
      + clear - X' IBIG D1 D2; lia.
      + clear - X' IBIG D1 D2; lia.
      + destruct Bq5 as [Yb|Yb]; clear - X' Yb D1 D2; lia.
      + destruct GFBIG as [Yb|Yb]; clear - X' Yb D1 D2 Eq Hg Hkk; lia.
    - intros a Hc Ho rr Hin Hr. destruct (WcR rr a Hin Hr) as [X'|[X'|[X'|[X'|X']]]].
      + apply (Ho (PMSP.o_src AD fb + 256, 40)); [unfold WR; wr_mem 1| wr_rng; clear - X' Eop; lia].
      + apply (Ho (PMSP.o_is AD fb + 40, 8)); [unfold WR; wr_mem 2| wr_rng; clear - X' Eois; lia].
      + apply (Ho (PMSP.o_is AD fb + 152, 4)); [unfold WR; wr_mem 3| wr_rng; clear - X' Eois; lia].
      + assert (Iq' : In (qc, 16384) (PEC.owned si en k)) by (unfold PEC.owned; apply in_or_app; left; unfold PM.parser_own, PM.src_own; left; reflexivity).
        exact (PMARS1.own_not_aclient L ar C HI HIok (PEC.owned si en k) LBX FF' LKi cri Awi Mi _ qc 16384 a sp 22528 HHi Iq' X' (L5SAR.aclient_cons L ar LBX FF (F, 2, sp - 128 + 32) sp 22528 a Hc)).
      + apply (GNCF a); [left; clear - X' Eq Hg Hkk; lia| exact Hc]. }
  pose proof (L5SAR.ek_callee L ar LBi [] FF [(F, 2, sp - 128 + 32)] sp 22528 (sp - 128) 20480 Wc Wc Mi M4 ltac:(rewrite app_nil_l; exact HP4) ltac:(clear; lia) ltac:(clear; lia) (fun a _ X' => X')) as EK4.
  assert (OUTc : forall a n, fb + 32 <= a -> a + n <= fb + 2040 -> (a + n <= op + 280 \/ op + 320 <= a) -> (a + n <= ois + 40 \/ ois + 48 <= a) ->
                 (a + n <= ois + 152 \/ ois + 156 <= a) -> forall i, a <= i < a + n -> L5.outside Wc i).
  { intros a n X1 X2 X3 X4 X5 i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|[Yc|Yc]]]]; [clear - Hi' Yc X3; lia| clear - Hi' Yc X4; lia| clear - Hi' Yc X5; lia| |].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ qc 16384 a n HHi Iq (PMAUAR.aobjA_push FF a n _ (AOF a n X1 X2))) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (APART a n 0 0 (CLfb a n X1 X2 ltac:(clear - Hi'; lia)) ltac:(clear - Hi'; lia)) as (Z' & _). change (ff_bytes 2) with 256 in Z'. clear - Hi' Yc Z' Eq Hg Hkk; lia. }
  assert (WAPPc : PMKA.wapp Wc).
  { intros rr Hin. unfold Wc, PMSPA.W_src, PMSPA.W_srcf, PMSPA.o_src, PMSPA.o_is, PMSPA.o_p in Hin. cbn [app pa_off_p pa_off_is AD PeCLayoutA.CADDR_A] in Hin. fold qc in Hin.
    unfold BIGSHADOW_LO, BIGSHADOW_HI. destruct Hin as [<-|[<-|[<-|[<-|[<-|[]]]]]]; cbn [fst snd]; unfold PM.CHUNK.
    - clear - OBIG Eop; lia.
    - clear - IBIG Eois; lia.
    - clear - IBIG Eois; lia.
    - destruct Bq5 as [Yb|Yb]; clear - Yb; lia.
    - destruct GFBIG as [Yb|Yb]; clear - Yb Eq Hg Hkk; lia. }
  assert (OUTBc : forall q' m, In (q', m) LBi -> q' <> qc -> forall i, q' <= i < q' + m -> L5.outside Wc i).
  { intros q' m Hq' NE i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|[Yc|Yc]]]].
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m op 384 HHi Hq' (PMAUAR.aobjA_push FF op 384 _ AOP)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq' (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - destruct (PMASK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q' m ois 272 HHi Hq' (PMAUAR.aobjA_push FF ois 272 _ AOI)) as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - pose proof (PMASK.blk_apart L ar C HI HIok _ _ _ _ _ _ _ q' m qc 16384 HHi Hq' Iq NE) as Z'. clear - Hi' Yc Z'; lia.
    - pose proof (WBi _ Hq') as (_ & _ & _ & _ & _ & _ & FA). cbn [fst snd] in FA.
      unfold FS_BYTES in FA, GFS1, GFS2. clear - Hi' Yc FA GFS1 GFS2 Eq Hg Hkk; lia. }
  assert (OUTcI : forall i, 0x674080 <= i < 0x695df4 -> L5.outside Wc i).
  { intros i Hi' rr Hin Hr. destruct (WcR rr i Hin Hr) as [Yc|[Yc|[Yc|[Yc|Yc]]]]; [clear - Hi' Yc O1; lia| clear - Hi' Yc I1; lia| clear - Hi' Yc I1; lia| |].
    - destruct Bqi as [Z'|Z']; clear - Hi' Yc Z'; lia.
    - clear - Hi' Yc GFR Eq Hg; lia. }

  assert (EA4 : PECA.enc_atA RSEGS EE L ar M4 ov fb en).
  { apply (PECFA.enc_keepA RSEGS EE L ar LBi FF sp 22528 Wc Mi M4 EK4 WAPPc FRB BRBi ov fb en (AOF ov 56 ltac:(lia) ltac:(lia))); [| exact EINC| | exact EA].
    - apply OUTc; clear - Eop Eov Eois; lia.
    - intros Hp. assert (INe : In (PEC.en_b en, PEC.ESZ * PEC.ecap (PEC.en_k en)) (PEC.enc_own en)).
      { unfold PEC.enc_own. replace (PEC.en_k en =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (EINC _ INe) _). apply (NEQ _ (PEC.ESZ * PEC.ecap (PEC.en_k en))). apply in_or_app. left. exact INe. }
  assert (VREF4 : L5.u64_at RSEGS M4 (op + 384) ov).
  { apply (PMKA.u64_keepA RSEGS L ar LBi FF sp 22528 Wc Mi M4 EK4 WAPPc FRB (op + 384) ov (AOF (op + 384) 8 ltac:(lia) ltac:(lia))); [| exact VREF].
    apply OUTc; clear - Eop Eois; lia. }
  assert (SKA4 : PESKA.sink_atA RSEGS L ar P M4 osk k).
  { apply (PECFA.sink_keepA RSEGS L ar LBi FF sp 22528 Wc Mi M4 EK4 WAPPc FRB BRBi P osk k (AOF osk 24 ltac:(lia) ltac:(lia))); [| exact KINC| | exact SKA].
    - apply OUTc; clear - Eop Eosk Eois; lia.
    - intros Hp. assert (INk : In (PESK.sk_b k, PESK.sk_c k) (PESK.sink_own k)).
      { unfold PESK.sink_own. replace (PESK.sk_c k =? 0) with false by (symmetry; apply Z.eqb_neq; lia). left. reflexivity. }
      refine (OUTBc _ _ (KINC _ INk) _). apply (NEQ _ (PESK.sk_c k)). apply in_or_app. right. apply in_or_app. left. exact INk. }
  assert (ERR4 : PESTA.err_okA RSEGS AD AAD EE M4 ei).
  { apply (PECFA.err_okA_keep RSEGS AD AAD EE L ar LBi FF sp 22528 Wc Mi M4 EK4 ei PECSA.addrs_wf_A); [| exact ERR].
    intros a D. change (PMST.dep PMA.AD a) in D. pose proof (PMASK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa).
    split; [clear - DI; lia|]. split; [exact (PMA.ly_static L C LY a (PnStatics.PNST.dep_of_j _ _ a D))|]. apply OUTcI; exact DI. }
  assert (BASE4 : PMSTA.base_okA RSEGS AD M4).
  { change (PMSTA.base_okA RSEGS PMA.AD M4). apply (PMASK.base_keep L ar C LY LBi FF sp 22528 Wc Mi M4 EK4); [| exact BASE].
    intros a Ha rr Hin Hr. destruct (WcR rr a Hin Hr) as [Yc|[Yc|[Yc|[Yc|Yc]]]]; [clear - Ha Yc O1; lia| clear - Ha Yc I1; lia| clear - Ha Yc I1; lia| destruct Bqi as [Z'|Z']; clear - Ha Yc Z'; lia| clear - Ha Yc GFR Eq Hg; lia]. }
  assert (ECS4 : PECA.ec_stateA RSEGS AD M4 fb (s_ec Y) cat).
  { apply (PECFA.ec_state_keepA RSEGS AD L ar LBi FF sp 22528 Wc Mi M4 EK4 WAPPc FRB fb (s_ec Y) cat (AOF oec 16 ltac:(lia) ltac:(lia))); [| exact ECS].
    fold oec. apply OUTc; clear - Eop Eoec Eois; lia. }
  assert (ACC4 : PMSPA.accA M4 op PECA.RDR_BYTES).
  { pose proof BI4 as (_ & _ & _ & _ & _ & _ & EKb4 & _).
    exact (PMKA.acc_keepA' L ar LBX FF sp 22528 WR M M4 EKb4 wappR FRB op 392 (AOF op 392 ltac:(lia) ltac:(lia)) (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 CPRE))))))))))))). }

  destruct RES4 as (CW4 & p' & k' & d & Yp & Yk & Hp1 & Hp2 & Hk' & Yd & Hd & CONS & SHORT & DEFd & BYT).
  assert (Ek : k' = kk).
  { rewrite L5K.rl12 in Yk. rewrite J12 in Yk. apply (f_equal bv_unsigned) in Yk. unfold PM.CHUNK in Hk'. rewrite !L5.unsigned_lit in Yk by (clear - Hk' Hkk; lia). clear - Yk; lia. }
  subst k'.
  assert (Ep : p' = q).
  { rewrite L5K.rl11 in Yp. rewrite J11 in Yp. apply (f_equal bv_unsigned) in Yp. rewrite !L5.unsigned_lit in Yp by (clear - Hp1 Hp2 Q0f GF2 Eq Hg Hkk; lia). clear - Yp; lia. }
  subst p'. rewrite L5K.rl10 in Yd.
  assert (QC4 : PM.sr_qc src4 = qc) by (destruct STEP4 as (X' & _); exact X').
  set (s4 := PMSPA.with_src si src4) in *.
  assert (EOWN : PM.parser_own s4 = PM.parser_own si) by (unfold s4, PMSPA.with_src, PM.parser_own, PM.src_own; cbn [PM.p_src PM.p_b PM.p_k PM.p_tb]; rewrite QC4; reflexivity).
  assert (EOWN4 : PEC.owned s4 en k = PEC.owned si en k) by (unfold PEC.owned; rewrite EOWN; reflexivity).

  assert (CONT4 : PEC.content_ok RSEGS AD M4 fb p src4 str sm4).
  { destruct CW4 as (CWP & CWB & CW5). pose proof IA as (_ & _ & _ & _ & _ & _ & _ & _ & _ & VS3 & _). pose proof VS3 as (_ & _ & VSF3).
    apply (PECF.content_ok_step RSEGS AD Mi M4 fb p (PM.p_src si) str smi src4 sm4); [clear - I1 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| clear - I3 Eois; unfold PMSP.o_is; cbn [pa_off_is AD PeCLayoutA.CADDR_A]; lia| | | | exact (proj1 CWP)| exact CWB| exact CW5| exact CONT].
    - unfold PMSP.o_is. cbn [pa_off_is AD PeCLayoutA.CADDR_A]. change (fb + 96) with ois.
      exact (proj1 (PMKA.agA_obj L ar LBi FF sp 22528 Wc Mi M4 EK4 WAPPc FRB (ois + 80) 24 (AOF (ois + 80) 24 ltac:(lia) ltac:(lia)) (OUTc (ois + 80) 24 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)))).
    - intros c0 n0 q0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. destruct VSF3 as (_ & _ & _ & Hn0 & Hc0 & _).
      assert (IN0 : In (q0, c0) LBi) by (apply SINC; unfold PM.vs_own; rewrite Es; left; reflexivity).
      destruct (BRBi _ IN0) as (B0' & B1'). cbn [fst snd] in B0', B1'.
      split; [exact B0'|]. split; [clear - B1'; lia|]. split; [clear - Hn0; lia|].
      refine (proj1 (PMKA.agA_blk L ar LBi FF sp 22528 Wc Mi M4 EK4 WAPPc BRBi q0 c0 IN0 _)).
      refine (OUTBc q0 c0 IN0 _). apply (NEQ q0 c0). apply in_or_app. right. apply in_or_app. right. apply INCS. unfold PM.vs_own. rewrite Es. left. reflexivity.
    - intros n0 Es. cbn in VSF3. rewrite Es in VSF3. cbn in VSF3. clear - VSF3. lia. }

  assert (UNR : PM.unread (PM.p_src si) smi = blen p - s_pos Y) by (unfold PEC.pos_of in POS; clear - POS; lia).
  unfold PMSPA.consumed in CONS.
  assert (LE : s_pos Y + d <= blen p).
  { destruct CW4 as (CWP & _). unfold PEC.pos_of in CWP. clear - CWP CONS UNR Hd. lia. }
  assert (SHORT' : d < kk -> s_pos Y + d = blen p).
  { intros Hdk. pose proof (SHORT Hdk) as U0. clear - U0 CONS UNR. lia. }
  rewrite POS in BYT.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr Ri (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved Ri R4 j RP4 Hj)).
  apply (KX fx4 R4 M4 md4 LK4 Aw4 src4 sm4 d RP4 Yd Hd SHORT' LE BYT).
  unfold amid. split; [| split; [rewrite <- EOWN4 in BI4; exact BI4| split; [| split; [| split; [exact EIMP| split]]]]].
  - split; [rewrite (R4c 2%nat) by inl; exact J2|]. split; [rewrite (R4c 8%nat) by inl; exact J8|]. split; [rewrite (R4c 9%nat) by inl; exact J9|].
    split; [rewrite (R4c 18%nat) by inl; exact J18|]. split; [rewrite (R4c 19%nat) by inl; exact J19|]. split; [rewrite (R4c 20%nat) by inl; exact J20|].
    split; [rewrite (R4c 21%nat) by inl; exact J21|]. split; [rewrite (R4c 24%nat) by inl; exact J24|]. split; [rewrite (R4c 25%nat) by inl; exact J25|].
    split; [rewrite (R4c 26%nat) by inl; exact J26|].
    intros j Hj. rewrite (R4c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity). apply J34. exact Hj.
  -
    unfold PECA.crun_preA. unfold s4, PMSPA.with_src. cbn [PM.p_src PM.p_tb PM.p_tg PM.p_b PM.p_k PM.p_more PM.p_done PM.p_depth PM.p_stk].
    split; [exact PA4|]. split; [exact IA4|]. split; [exact EA4|]. split; [exact VREF4|]. split; [exact SKA4|]. split; [exact BASE4|]. split; [exact ERR4|].
    split; [exact TBOK|]. split; [exact CONT4|].
    split.
    { unfold PEC.clink. cbn [s_more s_done s_depth s_stk s_pos s_estk s_edepth s_lo s_hi s_bad w_pos PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_src].
      split; [exact Lmore|]. split; [exact Ldone|]. split; [exact Ldepth|]. split; [exact Lstk|].
      split; [intros _ _; unfold PEC.pos_of; destruct CW4 as (CWP & _); unfold PEC.pos_of in CWP; clear - CONS UNR Hd; lia|].
      split; [exact Lestk|]. split; [exact Ledepth|]. split; [exact Lz| exact Lbad]. }
    split; [cbn [s_ec w_pos]; exact ECS4|]. split; [exact ECI| exact ACC4].
  - unfold s4, PMSPA.with_src. cbn [PM.p_src]. exact (PMAPAR.src_step_transA _ _ _ _ _ _ ST STEP4).
  - unfold PMSP.credit_keep, PECA.pot_allA, PEC.credit_add, PM.pot_parser, s4, PMSPA.with_src in CK |- *. cbn [PM.p_k PM.p_tb PM.p_tg fst snd] in CK |- *. exact CK.
  - unfold s4, PMSPA.with_src. cbn [PM.p_tb PM.p_tg PM.p_b PM.p_k]. exact TBK.
Qed.

Lemma tail_R fxi Ri Mi mdi LKi Awi cri si smi ei n pos1 (fx7 : FPState) R7 M7v (pci : Z) :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei (w_pos pos1 X) -> UbjRef.get_length p (s_pos X) = Some (n, pos1) ->
  msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 pci) (mrestrict (ahid Awi mdi) Mi) (seg_rom RSEGS)) (@mkst fx7 R7 (Z_to_bv 64 0xb63c0) M7v (seg_rom RSEGS)) ->
  mem_grows (mrestrict (ahid Awi mdi) Mi) M7v ->
  (forall i, 0 <= i < 2 ^ 64 -> ~ (F + 0 <= i < F + 0 + 8) -> ~ (F / 8 + 2147450880 + 0 <= i < F / 8 + 2147450880 + 0 + 32) -> ~ (fl + 0 <= i < fl + 0 + 1) ->
      M7v (Z_to_bv 64 i) = mrestrict (ahid Awi mdi) Mi (Z_to_bv 64 i)) ->
  (forall j, In j [3; 4; 27]%nat -> getr R7 (reg j) = getr Ri (reg j)) ->
  (forall j, In j [1; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26]%nat -> getr R7 (reg j) = getr R (reg j)) ->
  getr R7 (reg 2) = Z_to_bv 64 sp -> getr R7 (reg 10) = Z_to_bv 64 n -> L5.u8_at RSEGS M7v fl 0 ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri pci Mi mdi) K.
Proof.
  intros MID GL MS7 MG7 FRZ7 K347 REG7 E72 A0 FL0. entry_facts. frame_facts. open_amid MID.
  pose proof CP as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACC).
  set (Hi := ahid Awi mdi) in *. set (MVi := mrestrict Hi Mi) in *.
  vis_amid BI Hi MVi.
  assert (FOK' : PECA.frame_ok5 FF' fb) by exact (frame_ok5_push FF fb (F, 2, sp - 128 + 32) FOK).
  pose proof (PMAPAR.op_vis L ar C HI LY HIok _ _ LKi cri Awi Mi mdi fb _ si HHi FOK' PA) as ((_ & _ & _) & Zop & Z32 & Z20 & OWR & _ & OVIS & _ & _).
  fold Hi in Zop, Z32, Z20, OWR, OVIS. fold MVi in Zop, Z32, Z20, OWR.
  destruct (APART op 384 0 0) as (ApF & ApSF & ApFL).
  { intros i Hi'. unfold aclient, aclient_g. do 3 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 5) with 2048.
    split; [clear - Eop Hi'; lia| intros Y'; clear - Eop Hi' Y'; lia]. }
  { clear; lia. }
  change (ff_bytes 2) with 256 in ApF, ApSF. change (256 / 8) with 32 in ApSF. unfold SB in ApSF.
  assert (SHop : op / 8 + 2147450880 = fb / 8 + 2147450880 + 74).
  { rewrite Eop. pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
    replace (2048 * (fb / 2048) + 592) with ((256 * (fb / 2048) + 74) * 8) by (clear; lia). rewrite Z.div_mul by lia.
    replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
  destruct (APART (op / 8 + 2147450880) 48 0 0) as (_ & AsopSF & _).
  { intros i Hi'. unfold aclient, aclient_g. do 5 right; left. exists (fb, 5, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
    change (ff_bytes 5) with 2048. unfold in_shadow_of, S. unfold SB.
    assert (D1 : (fb + 2048 - 1) / 8 = fb / 8 + 255).
    { pose proof (Z.div_mod fb 2048 ltac:(lia)) as Dm. rewrite Fal, Z.add_0_r in Dm. rewrite Dm.
      replace (2048 * (fb / 2048) + 2048 - 1) with (7 + (256 * (fb / 2048) + 255) * 8) by (clear; lia). rewrite Z.div_add by lia.
      replace (2048 * (fb / 2048)) with ((256 * (fb / 2048)) * 8) by (clear; lia). rewrite Z.div_mul by lia. clear; lia. }
    rewrite D1. clear - SHop Hi'. lia. }
  { clear; lia. }
  change (256 / 8) with 32 in AsopSF. unfold SB in AsopSF.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  fold Hi in MS7, MG7, FRZ7. fold MVi in MS7, MG7, FRZ7.
  assert (R7ra : getr R7 (reg 1) = Z_to_bv 64 r) by (rewrite (REG7 1%nat) by inl; exact Rra).
  pose proof (PMK.ret_to RSEGS fx7 R7 M7v 0xb63c0 W_b6370 r F_b6370 eq_refl D_b6370 R7ra Hr1 Hr2) as MSr.
  apply (PMAUK.retire_coreW L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k) G
           WR (PEC.owned si en k) Mi mdi LKi cri Awi (fun _ => False) fxi fx7 Ri pci R7 r M7v K BI).
  { intros a []. }
  { intros a. right. intros []. }
  { exact (msteps_trans _ _ _ _ MS7 MSr). }
  { exact MG7. }
  { intros a Ha Nw. unfold PMAUK.WretX, PMAUK.Wret in Nw. change (ff_bytes 2) with 256 in Nw.
    apply FRZ7; [exact Ha| intros X'; apply Nw; left; left; left; clear - X'; lia| intros X'; apply Nw; left; left; right; unfold SB; clear - X'; lia
                | intros X'; apply Nw; left; right; clear - X'; lia]. }
  { exact FL0. }
  intros Mf modelf FZf MGf VISf AHf MRTf AMf HHf. change (mrestrict Hi Mf = M7v) in VISf.
  set (LBi := PEC.owned si en k ++ LBX) in *.
  assert (EKf : L5SAR.ek L ar LBi FF 0 0 [] Mi Mf).
  { apply (PMAUAR.wret_ek L ar C HI LY HIok LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k)
             LBi LKi cri Awi Mi Mf _ [] (fun _ => False) G HHi); [intros a []| exact FZf]. }
  pose proof (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HHi) as BRBi.
  apply (KONT fx7 R7 Mf modelf LKi Awi si smi ei cri).
  - apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
    repeat (destruct Hj as [<-|Hj]; [first [ rewrite E72; exact (eq_sym Rsp) | apply REG7; inl | rewrite (K347 _) by inl; apply J34; inl ] |]).
    destruct Hj.
  - unfold PECSPA.gl_post. rewrite GL.
    apply (cpre_keepA LBi 0 0 [] Mi Mf (w_pos pos1 X) si smi ei EKf PMKA.wapp_nil BRBi); [unfold LBi; apply incl_appl; apply incl_refl| unfold LBi; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CP].
  - unfold PECSPA.gl_ret. rewrite GL. rewrite L5K.rl10. exact A0.
  - exact ST.
  - exact EIMP.
  - exact (proj1 TBK).
  - exact (proj1 (proj2 TBK)).
  - exact (proj1 (proj2 (proj2 TBK))).
  - exact (proj2 (proj2 (proj2 TBK))).
  - exact AHf.
  - exact CK.
  - exact MRTf.
  - exact INCLi.
  - exact INCAi.
  - exact AMf.
  - exact HHf.
Qed.

Lemma arm_i fxi Ri Mi mdi LKi Awi cri si smi ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei (w_pos (s_pos X + 1) X) -> getr Ri (reg 10) = Z_to_bv 64 105 ->
  bat p (s_pos X) = 105 -> s_pos X + 1 <= blen p ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6058 Mi mdi) K.
Proof.
  intros MID1 A0 TB LE1.
  entry_facts. frame_facts.
  destruct MP as (BOK & PPOS & PMORE & PDONE & PHALT & PBAD).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (Q0g : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - GSLO GSHI GSPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - O1 O3 Eop Eoec; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  set (X1 := w_pos (s_pos X + 1) X) in *.
  pose proof MID1 as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI1 & _).
  pose proof BI1 as (HH1 & AM1 & MRT1 & _).
  set (H1 := ahid Awi mdi) in *. set (MV1 := mrestrict H1 Mi) in *.
  vis_amid BI1 H1 MV1.

  pose proof (PEAGLP1.aglTi_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT. cbn beta iota in PT.
  L5SAR.feed PT ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
  destruct PT as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y22 & Y23 & SHB3).
  apply (amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi ei X1 fx3 R3 0xb6058 (pa_src_read AD) M3v
           (fun a => F / 8 + 2147450880 + 6 <= a < F / 8 + 2147450880 + 6 + 1) MID1 MS3 MG3 FRZ3 ltac:(intros a Ha; cbv beta in Ha; unfold SB; clear - Ha; lia)
           ltac:(intros j Hj; apply KS3; revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity)).
  intros M3 md3 VIS3 HID3 MGM3 MID3.
  assert (SHB3' : L5.u8_at RSEGS (mrestrict (ahid Awi md3) M3) (F / 8 + 2147450880 + 6) 1).
  { replace (F / 8 + 2147450880 + 6) with (F / 8 + 2147450886) by (clear; lia). rewrite HID3, VIS3. exact SHB3. }

  apply (call_read (F + 48) 1 0xb6094 6 1 fx3 R3 M3 md3 LKi Awi cri si smi ei X1 MID3 PMORE PDONE ltac:(unfold X1; cbn [s_pos w_pos]; clear - PPOS LE1; lia)
           Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SHB3' ltac:(right; clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 d RP4 Z10 Hd SHORT LE BYT MID4.
  change (s_pos X1) with (s_pos X + 1) in SHORT, LE, BYT, MID4.
  set (si4 := PMSPA.with_src si src4) in *.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
  pose proof MID4 as ((K2 & K8 & K9 & K18 & K19 & K20 & K21 & K24 & K25 & K26 & K34) & BI4 & CP4 & _).
  pose proof BI4 as (HH4 & AM4 & MRT4 & _). pose proof AM4 as (Mh4 & MI4).
  clear WSi ICi CSBi CUARi OWNv FDi FWi FSWi FLCi FLWi FLCci FLVi VFi VSi VSHi.
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  vis_amid BI4 H4 MV4.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  assert (S22 : getr R4 (reg 22) = Z_to_bv 64 1) by (rewrite (R4c 22%nat) by inl; exact Y22).
  assert (S23 : getr R4 (reg 23) = Z_to_bv 64 (F + 48)) by (rewrite (R4c 23%nat) by inl; exact Y23).
  pose proof (PECGLW.gl_eval_s p (s_pos X) 105 1 ltac:(clear - LE1; lia) TB eq_refl ltac:(clear; lia) ltac:(clear; lia)) as GL.
  destruct (Z.eq_dec d 1) as [Ed|Nd].
  -
    subst d. replace (blen p <? s_pos X + 1 + 1) with false in GL by (symmetry; apply Z.ltb_ge; clear - LE; lia).
    assert (FD4 : L5.defined M4 (F + 48) 8) by (apply (L5.defined_sub M4 F 256); [exact (proj1 (L5A.defined_vis H4 M4 F 256 VFi) FDi)| clear; lia| clear; lia]).
    destruct (PMCG.u64_of_defined RSEGS M4 (F + 48) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD4) as (x & Hx & U64).
    assert (U64v : L5.u64_at RSEGS MV4 (F + 48) x).
    { exact (proj2 (L5A.u64_at_vis H4 M4 (F + 48) x (L5A.avis_sub H4 F 256 (F + 48) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia)) U64). }
    pose proof (PECRVD.slice_bytes p (s_pos X + 1) 1 BOK) as SLB.
    assert (SLEN : length (UbjRef.slice p (s_pos X + 1) 1) = 1%nat) by (pose proof (PECRVD.slice_length p (s_pos X + 1) 1 ltac:(clear - PPOS; lia) ltac:(clear; lia) LE); clear - H; lia).
    assert (LANE : forall i, (i < 1)%nat -> PECGLW.lane x i = nth i (UbjRef.slice p (s_pos X + 1) 1) 0).
    { intros i Hi. apply (PECGLW.lane_of_bytes RSEGS M4 (F + 48) x _ i ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) Hx U64 BYT ltac:(rewrite SLEN; clear; lia) SLB ltac:(rewrite SLEN; exact Hi)). }
    set (b0 := PECGLW.lane x 0) in *. set (b1 := PECGLW.lane x 1) in *. set (b2 := PECGLW.lane x 2) in *. set (b3 := PECGLW.lane x 3) in *.
    set (b4 := PECGLW.lane x 4) in *. set (b5 := PECGLW.lane x 5) in *. set (b6 := PECGLW.lane x 6) in *. set (b7 := PECGLW.lane x 7) in *.
    pose proof (PECGLW.lane_range x 0) as B0'. pose proof (PECGLW.lane_range x 1) as B1'. pose proof (PECGLW.lane_range x 2) as B2'. pose proof (PECGLW.lane_range x 3) as B3'.
    pose proof (PECGLW.lane_range x 4) as B4'. pose proof (PECGLW.lane_range x 5) as B5'. pose proof (PECGLW.lane_range x 6) as B6'. pose proof (PECGLW.lane_range x 7) as B7'.
    fold b0 in B0'. fold b1 in B1'. fold b2 in B2'. fold b3 in B3'. fold b4 in B4'. fold b5 in B5'. fold b6 in B6'. fold b7 in B7'.
    pose proof (LANE 0%nat ltac:(clear; lia)) as L0. rewrite (PECGLW.nth_slice p (s_pos X + 1) 1 0) in L0 by (clear - PPOS LE; lia). fold b0 in L0.
    replace (s_pos X + 1 + Z.of_nat 0) with (s_pos X + 1) in L0 by (clear; lia).

    pose proof (PEAGLWP.aglWi_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PW. cbn beta iota in PW.
    L5SAR.feed PW ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PW as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z10').
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    lazymatch type of Z10' with getr _ _ = AX2.edenot ?EEv _ =>
      rewrite (PECGLW.val_i b0 b1 b2 b3 b4 b5 b6 b7 (conj B0' (conj B1' (conj B2' (conj B3' (conj B4' (conj B5' (conj B6' B7'))))))) EEv (AX2.EVar 50)
                 ltac:(cbn [AX2.edenot AX2.ev]; rewrite (L5.unsigned_lit x Hx); symmetry; exact (PECGLW.xle_of_lanes x Hx))) in Z10' end.
    set (W := PECGLW.wi b0) in Z10'.
    assert (WRn : 0 <= W < 2 ^ 64) by (unfold W, PECGLW.wi; clear - B0' B1' B2' B3' B4' B5' B6' B7'; destruct (b0 <? 128); lia).
    rewrite (PECGLW.rd_be_1 p (s_pos X + 1)) in GL by (clear - PPOS LE; lia).
    rewrite <- L0 in GL.
    destruct (PECGLW.sgn1_cases b0 B0') as (SG1 & SG2). rewrite SG1 in GL.
    destruct (Z.ltb_spec W (2 ^ 63)) as [WS|WS].
    +
      assert (HB0 : b0 < 128) by (unfold W, PECGLW.wi in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; destruct (Z.ltb_spec b0 128); lia).
      rewrite (SG2 HB0) in GL. replace (128 <=? b0) with false in GL by (symmetry; apply Z.leb_gt; exact HB0).
      pose proof (PEAGLWP.aglSiP_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E2 & E8 & E9 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & FL0 & _).
      apply (tail_R fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ _ fx6 R6 M6v 0xb6094 MID4 GL (msteps_trans _ _ _ _ MS5 MS6) MG6 FRZ6).
      * intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
        apply KS5. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R6 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * rewrite (KS6 10%nat) by inl. rewrite Z10'. unfold W, PECGLW.wi. replace (b0 <? 128) with true by (symmetry; apply Z.ltb_lt; exact HB0). reflexivity.
      * exact FL0.
    +
      assert (HB0 : 128 <= b0) by (unfold W, PECGLW.wi in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; destruct (Z.ltb_spec b0 128); lia).
      replace (128 <=? b0) with true in GL by (symmetry; apply Z.leb_le; exact HB0).
      pose proof (PEAGLP2.aglSiN_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E10 & E11 & _).
      assert (E6 : M6v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx6 R4 0xb6094 R6 0xae310 MV4 K HH4 AM4 (msteps_trans _ _ _ _ MS5 MS6) (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + 1) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx6 R6 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity). apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb60b0 4 fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 E1 ltac:(split; [clear; lia| reflexivity]) E10 E11 ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb60b0 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zi_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
  -
    assert (DL : d < 1) by (clear - Hd Nd; lia).
    replace (blen p <? s_pos X + 1 + 1) with true in GL by (symmetry; apply Z.ltb_lt; clear - DL SHORT; lia).
    assert (D0 : d = 0) by (clear - Hd Nd; lia). subst d.
    pose proof (PEAGLP2.aglNi_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PN. cbn beta iota in PN.
    L5SAR.feed PN ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | clear - Hd DL; lia
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PN as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1' & Y10' & Y11').
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx5 R4 0xb6094 R5 0xae310 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + 0) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx5 R5 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb60b0 1 fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb60b0 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zi_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
Qed.

Lemma arm_I fxi Ri Mi mdi LKi Awi cri si smi ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei (w_pos (s_pos X + 1) X) -> getr Ri (reg 10) = Z_to_bv 64 73 ->
  bat p (s_pos X) = 73 -> s_pos X + 1 <= blen p ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6058 Mi mdi) K.
Proof.
  intros MID1 A0 TB LE1.
  entry_facts. frame_facts.
  destruct MP as (BOK & PPOS & PMORE & PDONE & PHALT & PBAD).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (Q0g : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - GSLO GSHI GSPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - O1 O3 Eop Eoec; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  set (X1 := w_pos (s_pos X + 1) X) in *.
  pose proof MID1 as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI1 & _).
  pose proof BI1 as (HH1 & AM1 & MRT1 & _).
  set (H1 := ahid Awi mdi) in *. set (MV1 := mrestrict H1 Mi) in *.
  vis_amid BI1 H1 MV1.

  pose proof (PEAGLP1.aglTI_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT. cbn beta iota in PT.
  L5SAR.feed PT ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
  destruct PT as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y22 & Y23 & SHB3).
  apply (amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi ei X1 fx3 R3 0xb6058 (pa_src_read AD) M3v
           (fun a => F / 8 + 2147450880 + 10 <= a < F / 8 + 2147450880 + 10 + 1) MID1 MS3 MG3 FRZ3 ltac:(intros a Ha; cbv beta in Ha; unfold SB; clear - Ha; lia)
           ltac:(intros j Hj; apply KS3; revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity)).
  intros M3 md3 VIS3 HID3 MGM3 MID3.
  assert (SHB3' : L5.u8_at RSEGS (mrestrict (ahid Awi md3) M3) (F / 8 + 2147450880 + 10) 2).
  { replace (F / 8 + 2147450880 + 10) with (F / 8 + 2147450890) by (clear; lia). rewrite HID3, VIS3. exact SHB3. }

  apply (call_read (F + 80) 2 0xb6248 10 2 fx3 R3 M3 md3 LKi Awi cri si smi ei X1 MID3 PMORE PDONE ltac:(unfold X1; cbn [s_pos w_pos]; clear - PPOS LE1; lia)
           Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SHB3' ltac:(right; clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 d RP4 Z10 Hd SHORT LE BYT MID4.
  change (s_pos X1) with (s_pos X + 1) in SHORT, LE, BYT, MID4.
  set (si4 := PMSPA.with_src si src4) in *.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
  pose proof MID4 as ((K2 & K8 & K9 & K18 & K19 & K20 & K21 & K24 & K25 & K26 & K34) & BI4 & CP4 & _).
  pose proof BI4 as (HH4 & AM4 & MRT4 & _). pose proof AM4 as (Mh4 & MI4).
  clear WSi ICi CSBi CUARi OWNv FDi FWi FSWi FLCi FLWi FLCci FLVi VFi VSi VSHi.
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  vis_amid BI4 H4 MV4.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  assert (S22 : getr R4 (reg 22) = Z_to_bv 64 (F + 80)) by (rewrite (R4c 22%nat) by inl; exact Y22).
  assert (S23 : getr R4 (reg 23) = Z_to_bv 64 2) by (rewrite (R4c 23%nat) by inl; exact Y23).
  pose proof (PECGLW.gl_eval_s p (s_pos X) 73 2 ltac:(clear - LE1; lia) TB eq_refl ltac:(clear; lia) ltac:(clear; lia)) as GL.
  destruct (Z.eq_dec d 2) as [Ed|Nd].
  -
    subst d. replace (blen p <? s_pos X + 1 + 2) with false in GL by (symmetry; apply Z.ltb_ge; clear - LE; lia).
    assert (FD4 : L5.defined M4 (F + 80) 8) by (apply (L5.defined_sub M4 F 256); [exact (proj1 (L5A.defined_vis H4 M4 F 256 VFi) FDi)| clear; lia| clear; lia]).
    destruct (PMCG.u64_of_defined RSEGS M4 (F + 80) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD4) as (x & Hx & U64).
    assert (U64v : L5.u64_at RSEGS MV4 (F + 80) x).
    { exact (proj2 (L5A.u64_at_vis H4 M4 (F + 80) x (L5A.avis_sub H4 F 256 (F + 80) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia)) U64). }
    pose proof (PECRVD.slice_bytes p (s_pos X + 1) 2 BOK) as SLB.
    assert (SLEN : length (UbjRef.slice p (s_pos X + 1) 2) = 2%nat) by (pose proof (PECRVD.slice_length p (s_pos X + 1) 2 ltac:(clear - PPOS; lia) ltac:(clear; lia) LE); clear - H; lia).
    assert (LANE : forall i, (i < 2)%nat -> PECGLW.lane x i = nth i (UbjRef.slice p (s_pos X + 1) 2) 0).
    { intros i Hi. apply (PECGLW.lane_of_bytes RSEGS M4 (F + 80) x _ i ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) Hx U64 BYT ltac:(rewrite SLEN; clear; lia) SLB ltac:(rewrite SLEN; exact Hi)). }
    set (b0 := PECGLW.lane x 0) in *. set (b1 := PECGLW.lane x 1) in *. set (b2 := PECGLW.lane x 2) in *. set (b3 := PECGLW.lane x 3) in *.
    set (b4 := PECGLW.lane x 4) in *. set (b5 := PECGLW.lane x 5) in *. set (b6 := PECGLW.lane x 6) in *. set (b7 := PECGLW.lane x 7) in *.
    pose proof (PECGLW.lane_range x 0) as B0'. pose proof (PECGLW.lane_range x 1) as B1'. pose proof (PECGLW.lane_range x 2) as B2'. pose proof (PECGLW.lane_range x 3) as B3'.
    pose proof (PECGLW.lane_range x 4) as B4'. pose proof (PECGLW.lane_range x 5) as B5'. pose proof (PECGLW.lane_range x 6) as B6'. pose proof (PECGLW.lane_range x 7) as B7'.
    fold b0 in B0'. fold b1 in B1'. fold b2 in B2'. fold b3 in B3'. fold b4 in B4'. fold b5 in B5'. fold b6 in B6'. fold b7 in B7'.
    pose proof (LANE 0%nat ltac:(clear; lia)) as L0. rewrite (PECGLW.nth_slice p (s_pos X + 1) 2 0) in L0 by (clear - PPOS LE; lia). fold b0 in L0.
    replace (s_pos X + 1 + Z.of_nat 0) with (s_pos X + 1) in L0 by (clear; lia).
    pose proof (LANE 1%nat ltac:(clear; lia)) as L1. rewrite (PECGLW.nth_slice p (s_pos X + 1) 2 1) in L1 by (clear - PPOS LE; lia). fold b1 in L1.
    replace (s_pos X + 1 + Z.of_nat 1) with (s_pos X + 1 + 1) in L1 by (clear; lia).

    pose proof (PEAGLWP.aglWI_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PW. cbn beta iota in PW.
    L5SAR.feed PW ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PW as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z10' & _).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    lazymatch type of Z10' with getr _ _ = AX2.edenot ?EEv _ =>
      rewrite (PECGLW.val_I b0 b1 b2 b3 b4 b5 b6 b7 (conj B0' (conj B1' (conj B2' (conj B3' (conj B4' (conj B5' (conj B6' B7'))))))) EEv (AX2.EVar 50)
                 ltac:(cbn [AX2.edenot AX2.ev]; rewrite (L5.unsigned_lit x Hx); symmetry; exact (PECGLW.xle_of_lanes x Hx))) in Z10' end.
    set (W := PECGLW.wI b0 b1) in Z10'.
    assert (WRn : 0 <= W < 2 ^ 64) by (unfold W, PECGLW.wI; clear - B0' B1' B2' B3' B4' B5' B6' B7'; lia).
    rewrite (PECGLW.rd_be_2 p (s_pos X + 1)) in GL by (clear - PPOS LE; lia).
    rewrite <- L0, <- L1 in GL.
    destruct (PECGLW.sgn2_cases b0 b1 B0' B1') as (SG1 & SG2). rewrite SG1 in GL.
    destruct (Z.ltb_spec W (2 ^ 63)) as [WS|WS].
    +
      assert (HB0 : b0 < 128) by (unfold W, PECGLW.wI in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; lia).
      rewrite (SG2 HB0) in GL. replace (128 <=? b0) with false in GL by (symmetry; apply Z.leb_gt; exact HB0).
      pose proof (PEAGLWP.aglSIP_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & FL0 & _).
      apply (tail_R fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ _ fx6 R6 M6v 0xb6248 MID4 GL (msteps_trans _ _ _ _ MS5 MS6) MG6 FRZ6).
      * intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
        apply KS5. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R6 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * lazymatch type of E10 with context [AX2.edenot ?EEx _] => rewrite (PECGLW.sra48_of EEx (AX2.EVar 49) W ltac:(clear - WRn WS; lia) eq_refl) in E10 end. rewrite E10. unfold W, PECGLW.wI. rewrite (PECGLW.wI_shift b0 b1 B0' B1'). reflexivity.
      * exact FL0.
    +
      assert (HB0 : 128 <= b0) by (unfold W, PECGLW.wI in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; lia).
      replace (128 <=? b0) with true in GL by (symmetry; apply Z.leb_le; exact HB0).
      pose proof (PEAGLP2.aglSIN_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E10 & E11).
      assert (E6 : M6v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx6 R4 0xb6248 R6 0xae310 MV4 K HH4 AM4 (msteps_trans _ _ _ _ MS5 MS6) (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + 2) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx6 R6 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity). apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb6478 4 fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 E1 ltac:(split; [clear; lia| reflexivity]) E10 E11 ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb6478 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zI_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
  -
    assert (DL : d < 2) by (clear - Hd Nd; lia).
    replace (blen p <? s_pos X + 1 + 2) with true in GL by (symmetry; apply Z.ltb_lt; clear - DL SHORT; lia).
    pose proof (PEAGLP2.aglNI_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => d | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PN. cbn beta iota in PN.
    L5SAR.feed PN ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | clear - Hd DL; lia
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PN as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1' & Y10' & Y11').
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx5 R4 0xb6248 R5 0xae310 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + d) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx5 R5 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb6478 1 fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb6478 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zI_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
Qed.

Lemma arm_l fxi Ri Mi mdi LKi Awi cri si smi ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei (w_pos (s_pos X + 1) X) -> getr Ri (reg 10) = Z_to_bv 64 108 ->
  bat p (s_pos X) = 108 -> s_pos X + 1 <= blen p ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6058 Mi mdi) K.
Proof.
  intros MID1 A0 TB LE1.
  entry_facts. frame_facts.
  destruct MP as (BOK & PPOS & PMORE & PDONE & PHALT & PBAD).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (Q0g : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - GSLO GSHI GSPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - O1 O3 Eop Eoec; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  set (X1 := w_pos (s_pos X + 1) X) in *.
  pose proof MID1 as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI1 & _).
  pose proof BI1 as (HH1 & AM1 & MRT1 & _).
  set (H1 := ahid Awi mdi) in *. set (MV1 := mrestrict H1 Mi) in *.
  vis_amid BI1 H1 MV1.

  pose proof (PEAGLP1.aglTl_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT. cbn beta iota in PT.
  L5SAR.feed PT ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
  destruct PT as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y22 & Y23 & SHB3).
  apply (amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi ei X1 fx3 R3 0xb6058 (pa_src_read AD) M3v
           (fun a => F / 8 + 2147450880 + 12 <= a < F / 8 + 2147450880 + 12 + 1) MID1 MS3 MG3 FRZ3 ltac:(intros a Ha; cbv beta in Ha; unfold SB; clear - Ha; lia)
           ltac:(intros j Hj; apply KS3; revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity)).
  intros M3 md3 VIS3 HID3 MGM3 MID3.
  assert (SHB3' : L5.u8_at RSEGS (mrestrict (ahid Awi md3) M3) (F / 8 + 2147450880 + 12) 4).
  { replace (F / 8 + 2147450880 + 12) with (F / 8 + 2147450892) by (clear; lia). rewrite HID3, VIS3. exact SHB3. }

  apply (call_read (F + 96) 4 0xb61f0 12 4 fx3 R3 M3 md3 LKi Awi cri si smi ei X1 MID3 PMORE PDONE ltac:(unfold X1; cbn [s_pos w_pos]; clear - PPOS LE1; lia)
           Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SHB3' ltac:(right; clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 d RP4 Z10 Hd SHORT LE BYT MID4.
  change (s_pos X1) with (s_pos X + 1) in SHORT, LE, BYT, MID4.
  set (si4 := PMSPA.with_src si src4) in *.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
  pose proof MID4 as ((K2 & K8 & K9 & K18 & K19 & K20 & K21 & K24 & K25 & K26 & K34) & BI4 & CP4 & _).
  pose proof BI4 as (HH4 & AM4 & MRT4 & _). pose proof AM4 as (Mh4 & MI4).
  clear WSi ICi CSBi CUARi OWNv FDi FWi FSWi FLCi FLWi FLCci FLVi VFi VSi VSHi.
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  vis_amid BI4 H4 MV4.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  assert (S22 : getr R4 (reg 22) = Z_to_bv 64 4) by (rewrite (R4c 22%nat) by inl; exact Y22).
  assert (S23 : getr R4 (reg 23) = Z_to_bv 64 (F + 96)) by (rewrite (R4c 23%nat) by inl; exact Y23).
  pose proof (PECGLW.gl_eval_s p (s_pos X) 108 4 ltac:(clear - LE1; lia) TB eq_refl ltac:(clear; lia) ltac:(clear; lia)) as GL.
  destruct (Z.eq_dec d 4) as [Ed|Nd].
  -
    subst d. replace (blen p <? s_pos X + 1 + 4) with false in GL by (symmetry; apply Z.ltb_ge; clear - LE; lia).
    assert (FD4 : L5.defined M4 (F + 96) 8) by (apply (L5.defined_sub M4 F 256); [exact (proj1 (L5A.defined_vis H4 M4 F 256 VFi) FDi)| clear; lia| clear; lia]).
    destruct (PMCG.u64_of_defined RSEGS M4 (F + 96) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD4) as (x & Hx & U64).
    assert (U64v : L5.u64_at RSEGS MV4 (F + 96) x).
    { exact (proj2 (L5A.u64_at_vis H4 M4 (F + 96) x (L5A.avis_sub H4 F 256 (F + 96) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia)) U64). }
    pose proof (PECRVD.slice_bytes p (s_pos X + 1) 4 BOK) as SLB.
    assert (SLEN : length (UbjRef.slice p (s_pos X + 1) 4) = 4%nat) by (pose proof (PECRVD.slice_length p (s_pos X + 1) 4 ltac:(clear - PPOS; lia) ltac:(clear; lia) LE); clear - H; lia).
    assert (LANE : forall i, (i < 4)%nat -> PECGLW.lane x i = nth i (UbjRef.slice p (s_pos X + 1) 4) 0).
    { intros i Hi. apply (PECGLW.lane_of_bytes RSEGS M4 (F + 96) x _ i ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) Hx U64 BYT ltac:(rewrite SLEN; clear; lia) SLB ltac:(rewrite SLEN; exact Hi)). }
    set (b0 := PECGLW.lane x 0) in *. set (b1 := PECGLW.lane x 1) in *. set (b2 := PECGLW.lane x 2) in *. set (b3 := PECGLW.lane x 3) in *.
    set (b4 := PECGLW.lane x 4) in *. set (b5 := PECGLW.lane x 5) in *. set (b6 := PECGLW.lane x 6) in *. set (b7 := PECGLW.lane x 7) in *.
    pose proof (PECGLW.lane_range x 0) as B0'. pose proof (PECGLW.lane_range x 1) as B1'. pose proof (PECGLW.lane_range x 2) as B2'. pose proof (PECGLW.lane_range x 3) as B3'.
    pose proof (PECGLW.lane_range x 4) as B4'. pose proof (PECGLW.lane_range x 5) as B5'. pose proof (PECGLW.lane_range x 6) as B6'. pose proof (PECGLW.lane_range x 7) as B7'.
    fold b0 in B0'. fold b1 in B1'. fold b2 in B2'. fold b3 in B3'. fold b4 in B4'. fold b5 in B5'. fold b6 in B6'. fold b7 in B7'.
    pose proof (LANE 0%nat ltac:(clear; lia)) as L0. rewrite (PECGLW.nth_slice p (s_pos X + 1) 4 0) in L0 by (clear - PPOS LE; lia). fold b0 in L0.
    replace (s_pos X + 1 + Z.of_nat 0) with (s_pos X + 1) in L0 by (clear; lia).
    pose proof (LANE 1%nat ltac:(clear; lia)) as L1. rewrite (PECGLW.nth_slice p (s_pos X + 1) 4 1) in L1 by (clear - PPOS LE; lia). fold b1 in L1.
    replace (s_pos X + 1 + Z.of_nat 1) with (s_pos X + 1 + 1) in L1 by (clear; lia).
    pose proof (LANE 2%nat ltac:(clear; lia)) as L2. rewrite (PECGLW.nth_slice p (s_pos X + 1) 4 2) in L2 by (clear - PPOS LE; lia). fold b2 in L2.
    replace (s_pos X + 1 + Z.of_nat 2) with (s_pos X + 1 + 1 + 1) in L2 by (clear; lia).
    pose proof (LANE 3%nat ltac:(clear; lia)) as L3. rewrite (PECGLW.nth_slice p (s_pos X + 1) 4 3) in L3 by (clear - PPOS LE; lia). fold b3 in L3.
    replace (s_pos X + 1 + Z.of_nat 3) with (s_pos X + 1 + 1 + 1 + 1) in L3 by (clear; lia).

    pose proof (PEAGLWP.aglWl_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PW. cbn beta iota in PW.
    L5SAR.feed PW ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PW as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z10' & _).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    lazymatch type of Z10' with getr _ _ = AX2.edenot ?EEv _ =>
      rewrite (PECGLW.val_l b0 b1 b2 b3 b4 b5 b6 b7 (conj B0' (conj B1' (conj B2' (conj B3' (conj B4' (conj B5' (conj B6' B7'))))))) EEv (AX2.EVar 50)
                 ltac:(cbn [AX2.edenot AX2.ev]; rewrite (L5.unsigned_lit x Hx); symmetry; exact (PECGLW.xle_of_lanes x Hx))) in Z10' end.
    set (W := PECGLW.wl b0 b1 b2 b3) in Z10'.
    assert (WRn : 0 <= W < 2 ^ 64) by (unfold W, PECGLW.wl, PECGLW.be4; clear - B0' B1' B2' B3' B4' B5' B6' B7'; destruct (b0 <? 128); lia).
    rewrite (PECGLW.rd_be_4 p (s_pos X + 1)) in GL by (clear - PPOS LE; lia).
    rewrite <- L0, <- L1, <- L2, <- L3 in GL.
    destruct (PECGLW.sgn4_cases b0 b1 b2 b3 B0' B1' B2' B3') as (SG1 & SG2). rewrite SG1 in GL.
    destruct (Z.ltb_spec W (2 ^ 63)) as [WS|WS].
    +
      assert (HB0 : b0 < 128) by (unfold W, PECGLW.wl, PECGLW.be4 in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; destruct (Z.ltb_spec b0 128); lia).
      rewrite (SG2 HB0) in GL. replace (128 <=? b0) with false in GL by (symmetry; apply Z.leb_gt; exact HB0).
      pose proof (PEAGLWP.aglSlP_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E2 & E8 & E9 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & FL0 & _).
      apply (tail_R fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ _ fx6 R6 M6v 0xb61f0 MID4 GL (msteps_trans _ _ _ _ MS5 MS6) MG6 FRZ6).
      * intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
        apply KS5. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R6 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * rewrite (KS6 10%nat) by inl. rewrite Z10'. unfold W, PECGLW.wl, PECGLW.be4. replace (b0 <? 128) with true by (symmetry; apply Z.ltb_lt; exact HB0). reflexivity.
      * exact FL0.
    +
      assert (HB0 : 128 <= b0) by (unfold W, PECGLW.wl, PECGLW.be4 in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; destruct (Z.ltb_spec b0 128); lia).
      replace (128 <=? b0) with true in GL by (symmetry; apply Z.leb_le; exact HB0).
      pose proof (PEAGLP2.aglSlN_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E10 & E11).
      assert (E6 : M6v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx6 R4 0xb61f0 R6 0xae310 MV4 K HH4 AM4 (msteps_trans _ _ _ _ MS5 MS6) (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + 4) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx6 R6 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity). apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb63d4 4 fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 E1 ltac:(split; [clear; lia| reflexivity]) E10 E11 ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb63d4 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zl_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
  -
    assert (DL : d < 4) by (clear - Hd Nd; lia).
    replace (blen p <? s_pos X + 1 + 4) with true in GL by (symmetry; apply Z.ltb_lt; clear - DL SHORT; lia).
    pose proof (PEAGLP2.aglNl_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => d | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PN. cbn beta iota in PN.
    L5SAR.feed PN ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | clear - Hd DL; lia
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PN as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1' & Y10' & Y11' & _).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx5 R4 0xb61f0 R5 0xae310 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + d) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx5 R5 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb63d4 1 fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb63d4 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zl_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
Qed.

Lemma arm_L fxi Ri Mi mdi LKi Awi cri si smi ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei (w_pos (s_pos X + 1) X) -> getr Ri (reg 10) = Z_to_bv 64 76 ->
  bat p (s_pos X) = 76 -> s_pos X + 1 <= blen p ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6058 Mi mdi) K.
Proof.
  intros MID1 A0 TB LE1.
  entry_facts. frame_facts.
  destruct MP as (BOK & PPOS & PMORE & PDONE & PHALT & PBAD).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (Q0g : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - GSLO GSHI GSPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - O1 O3 Eop Eoec; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  set (X1 := w_pos (s_pos X + 1) X) in *.
  pose proof MID1 as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI1 & _).
  pose proof BI1 as (HH1 & AM1 & MRT1 & _).
  set (H1 := ahid Awi mdi) in *. set (MV1 := mrestrict H1 Mi) in *.
  vis_amid BI1 H1 MV1.

  pose proof (PEAGLP1.aglTL_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT. cbn beta iota in PT.
  L5SAR.feed PT ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
  destruct PT as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y22 & Y23 & SHB3).
  apply (amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi ei X1 fx3 R3 0xb6058 (pa_src_read AD) M3v
           (fun a => F / 8 + 2147450880 + 14 <= a < F / 8 + 2147450880 + 14 + 1) MID1 MS3 MG3 FRZ3 ltac:(intros a Ha; cbv beta in Ha; unfold SB; clear - Ha; lia)
           ltac:(intros j Hj; apply KS3; revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity)).
  intros M3 md3 VIS3 HID3 MGM3 MID3.
  assert (SHB3' : L5.u8_at RSEGS (mrestrict (ahid Awi md3) M3) (F / 8 + 2147450880 + 14) 0).
  { replace (F / 8 + 2147450880 + 14) with (F / 8 + 2147450894) by (clear; lia). rewrite HID3, VIS3. exact SHB3. }

  apply (call_read (F + 112) 8 0xb6134 14 0 fx3 R3 M3 md3 LKi Awi cri si smi ei X1 MID3 PMORE PDONE ltac:(unfold X1; cbn [s_pos w_pos]; clear - PPOS LE1; lia)
           Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SHB3' ltac:(left; reflexivity)).
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 d RP4 Z10 Hd SHORT LE BYT MID4.
  change (s_pos X1) with (s_pos X + 1) in SHORT, LE, BYT, MID4.
  set (si4 := PMSPA.with_src si src4) in *.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
  pose proof MID4 as ((K2 & K8 & K9 & K18 & K19 & K20 & K21 & K24 & K25 & K26 & K34) & BI4 & CP4 & _).
  pose proof BI4 as (HH4 & AM4 & MRT4 & _). pose proof AM4 as (Mh4 & MI4).
  clear WSi ICi CSBi CUARi OWNv FDi FWi FSWi FLCi FLWi FLCci FLVi VFi VSi VSHi.
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  vis_amid BI4 H4 MV4.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  assert (S22 : getr R4 (reg 22) = Z_to_bv 64 (F + 112)) by (rewrite (R4c 22%nat) by inl; exact Y22).
  assert (S23 : getr R4 (reg 23) = Z_to_bv 64 8) by (rewrite (R4c 23%nat) by inl; exact Y23).
  pose proof (PECGLW.gl_eval_s p (s_pos X) 76 8 ltac:(clear - LE1; lia) TB eq_refl ltac:(clear; lia) ltac:(clear; lia)) as GL.
  destruct (Z.eq_dec d 8) as [Ed|Nd].
  -
    subst d. replace (blen p <? s_pos X + 1 + 8) with false in GL by (symmetry; apply Z.ltb_ge; clear - LE; lia).
    assert (FD4 : L5.defined M4 (F + 112) 8) by (apply (L5.defined_sub M4 F 256); [exact (proj1 (L5A.defined_vis H4 M4 F 256 VFi) FDi)| clear; lia| clear; lia]).
    destruct (PMCG.u64_of_defined RSEGS M4 (F + 112) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD4) as (x & Hx & U64).
    assert (U64v : L5.u64_at RSEGS MV4 (F + 112) x).
    { exact (proj2 (L5A.u64_at_vis H4 M4 (F + 112) x (L5A.avis_sub H4 F 256 (F + 112) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia)) U64). }
    pose proof (PECRVD.slice_bytes p (s_pos X + 1) 8 BOK) as SLB.
    assert (SLEN : length (UbjRef.slice p (s_pos X + 1) 8) = 8%nat) by (pose proof (PECRVD.slice_length p (s_pos X + 1) 8 ltac:(clear - PPOS; lia) ltac:(clear; lia) LE); clear - H; lia).
    assert (LANE : forall i, (i < 8)%nat -> PECGLW.lane x i = nth i (UbjRef.slice p (s_pos X + 1) 8) 0).
    { intros i Hi. apply (PECGLW.lane_of_bytes RSEGS M4 (F + 112) x _ i ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) Hx U64 BYT ltac:(rewrite SLEN; clear; lia) SLB ltac:(rewrite SLEN; exact Hi)). }
    set (b0 := PECGLW.lane x 0) in *. set (b1 := PECGLW.lane x 1) in *. set (b2 := PECGLW.lane x 2) in *. set (b3 := PECGLW.lane x 3) in *.
    set (b4 := PECGLW.lane x 4) in *. set (b5 := PECGLW.lane x 5) in *. set (b6 := PECGLW.lane x 6) in *. set (b7 := PECGLW.lane x 7) in *.
    pose proof (PECGLW.lane_range x 0) as B0'. pose proof (PECGLW.lane_range x 1) as B1'. pose proof (PECGLW.lane_range x 2) as B2'. pose proof (PECGLW.lane_range x 3) as B3'.
    pose proof (PECGLW.lane_range x 4) as B4'. pose proof (PECGLW.lane_range x 5) as B5'. pose proof (PECGLW.lane_range x 6) as B6'. pose proof (PECGLW.lane_range x 7) as B7'.
    fold b0 in B0'. fold b1 in B1'. fold b2 in B2'. fold b3 in B3'. fold b4 in B4'. fold b5 in B5'. fold b6 in B6'. fold b7 in B7'.
    pose proof (LANE 0%nat ltac:(clear; lia)) as L0. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 0) in L0 by (clear - PPOS LE; lia). fold b0 in L0.
    replace (s_pos X + 1 + Z.of_nat 0) with (s_pos X + 1) in L0 by (clear; lia).
    pose proof (LANE 1%nat ltac:(clear; lia)) as L1. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 1) in L1 by (clear - PPOS LE; lia). fold b1 in L1.
    replace (s_pos X + 1 + Z.of_nat 1) with (s_pos X + 1 + 1) in L1 by (clear; lia).
    pose proof (LANE 2%nat ltac:(clear; lia)) as L2. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 2) in L2 by (clear - PPOS LE; lia). fold b2 in L2.
    replace (s_pos X + 1 + Z.of_nat 2) with (s_pos X + 1 + 1 + 1) in L2 by (clear; lia).
    pose proof (LANE 3%nat ltac:(clear; lia)) as L3. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 3) in L3 by (clear - PPOS LE; lia). fold b3 in L3.
    replace (s_pos X + 1 + Z.of_nat 3) with (s_pos X + 1 + 1 + 1 + 1) in L3 by (clear; lia).
    pose proof (LANE 4%nat ltac:(clear; lia)) as L4. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 4) in L4 by (clear - PPOS LE; lia). fold b4 in L4.
    replace (s_pos X + 1 + Z.of_nat 4) with (s_pos X + 1 + 1 + 1 + 1 + 1) in L4 by (clear; lia).
    pose proof (LANE 5%nat ltac:(clear; lia)) as L5. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 5) in L5 by (clear - PPOS LE; lia). fold b5 in L5.
    replace (s_pos X + 1 + Z.of_nat 5) with (s_pos X + 1 + 1 + 1 + 1 + 1 + 1) in L5 by (clear; lia).
    pose proof (LANE 6%nat ltac:(clear; lia)) as L6. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 6) in L6 by (clear - PPOS LE; lia). fold b6 in L6.
    replace (s_pos X + 1 + Z.of_nat 6) with (s_pos X + 1 + 1 + 1 + 1 + 1 + 1 + 1) in L6 by (clear; lia).
    pose proof (LANE 7%nat ltac:(clear; lia)) as L7. rewrite (PECGLW.nth_slice p (s_pos X + 1) 8 7) in L7 by (clear - PPOS LE; lia). fold b7 in L7.
    replace (s_pos X + 1 + Z.of_nat 7) with (s_pos X + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) in L7 by (clear; lia).

    pose proof (PEAGLWP.aglWL_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PW. cbn beta iota in PW.
    L5SAR.feed PW ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PW as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z10' & _).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    lazymatch type of Z10' with getr _ _ = AX2.edenot ?EEv _ =>
      rewrite (PECGLW.val_L b0 b1 b2 b3 b4 b5 b6 b7 (conj B0' (conj B1' (conj B2' (conj B3' (conj B4' (conj B5' (conj B6' B7'))))))) EEv (AX2.EVar 50)
                 ltac:(cbn [AX2.edenot AX2.ev]; rewrite (L5.unsigned_lit x Hx); symmetry; exact (PECGLW.xle_of_lanes x Hx))) in Z10' end.
    set (W := PECGLW.be8 b0 b1 b2 b3 b4 b5 b6 b7) in Z10'.
    assert (WRn : 0 <= W < 2 ^ 64) by (unfold W, PECGLW.be8; clear - B0' B1' B2' B3' B4' B5' B6' B7'; lia).
    rewrite (PECGLW.rd_be_8 p (s_pos X + 1)) in GL by (clear - PPOS LE; lia).
    rewrite <- L0, <- L1, <- L2, <- L3, <- L4, <- L5, <- L6, <- L7 in GL. change (b0 * 2 ^ 56 + b1 * 2 ^ 48 + b2 * 2 ^ 40 + b3 * 2 ^ 32 + b4 * 2 ^ 24 + b5 * 2 ^ 16 + b6 * 2 ^ 8 + b7) with (PECGLW.be8 b0 b1 b2 b3 b4 b5 b6 b7) in GL.
    destruct (PECGLW.sgn8_cases b0 b1 b2 b3 b4 b5 b6 b7 B0' B1' B2' B3' B4' B5' B6' B7') as (SG1 & SG2). rewrite SG1 in GL.
    destruct (Z.ltb_spec W (2 ^ 63)) as [WS|WS].
    +
      assert (HB0 : b0 < 128) by (unfold W, PECGLW.be8 in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; lia).
      rewrite (SG2 HB0) in GL. replace (128 <=? b0) with false in GL by (symmetry; apply Z.leb_gt; exact HB0).
      pose proof (PEAGLWP.aglSLP_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E2 & E8 & E9 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & FL0 & _).
      apply (tail_R fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ _ fx6 R6 M6v 0xb6134 MID4 GL (msteps_trans _ _ _ _ MS5 MS6) MG6 FRZ6).
      * intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
        apply KS5. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity.
      * intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R6 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
      * exact E2.
      * rewrite (KS6 10%nat) by inl. unfold W in Z10'. exact Z10'.
      * exact FL0.
    +
      assert (HB0 : 128 <= b0) by (unfold W, PECGLW.be8 in WS; clear - WS B0' B1' B2' B3' B4' B5' B6' B7'; lia).
      replace (128 <=? b0) with true in GL by (symmetry; apply Z.leb_le; exact HB0).
      pose proof (PEAGLP2.aglSLN_conc fx5 R5 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => W | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PX. cbn beta iota in PX.
      L5SAR.feed PX ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | first [rewrite KS5 by inl; assumption | clear - WS WRn; lia]
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
      destruct PX as (fx6 & R6 & M6v & MG6 & _ & FRZ6 & MS6 & KS6 & E1 & E10 & E11).
      assert (E6 : M6v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ6; exact Ha). subst M6v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx6 R4 0xb6134 R6 0xae310 MV4 K HH4 AM4 (msteps_trans _ _ _ _ MS5 MS6) (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + 8) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx6 R6 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. rewrite (KS6 j) by (revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity). apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb6410 4 fx6 R6 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 E1 ltac:(split; [clear; lia| reflexivity]) E10 E11 ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb6410 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zL_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
  -
    assert (DL : d < 8) by (clear - Hd Nd; lia).
    replace (blen p <? s_pos X + 1 + 8) with true in GL by (symmetry; apply Z.ltb_lt; clear - DL SHORT; lia).
    pose proof (PEAGLP2.aglNL_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => d | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PN. cbn beta iota in PN.
    L5SAR.feed PN ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | clear - Hd DL; lia
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PN as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1' & Y10' & Y11').
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx5 R4 0xb6134 R5 0xae310 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + d) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx5 R5 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb6410 1 fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb6410 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zL_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
Qed.

Lemma arm_U fxi Ri Mi mdi LKi Awi cri si smi ei :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei (w_pos (s_pos X + 1) X) -> getr Ri (reg 10) = Z_to_bv 64 85 ->
  bat p (s_pos X) = 85 -> s_pos X + 1 <= blen p ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6058 Mi mdi) K.
Proof.
  intros MID1 A0 TB LE1.
  entry_facts. frame_facts.
  destruct MP as (BOK & PPOS & PMORE & PDONE & PHALT & PBAD).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (Q0g : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - GSLO GSHI GSPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - O1 O3 Eop Eoec; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  set (X1 := w_pos (s_pos X + 1) X) in *.
  pose proof MID1 as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI1 & _).
  pose proof BI1 as (HH1 & AM1 & MRT1 & _).
  set (H1 := ahid Awi mdi) in *. set (MV1 := mrestrict H1 Mi) in *.
  vis_amid BI1 H1 MV1.

  pose proof (PEAGLP1.aglTU_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT. cbn beta iota in PT.
  L5SAR.feed PT ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
  destruct PT as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & Y22 & SHB3).
  apply (amid_pieceF fxi Ri Mi mdi LKi Awi cri si smi ei X1 fx3 R3 0xb6058 (pa_src_read AD) M3v
           (fun a => F / 8 + 2147450880 + 8 <= a < F / 8 + 2147450880 + 8 + 1) MID1 MS3 MG3 FRZ3 ltac:(intros a Ha; cbv beta in Ha; unfold SB; clear - Ha; lia)
           ltac:(intros j Hj; apply KS3; revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity)).
  intros M3 md3 VIS3 HID3 MGM3 MID3.
  assert (SHB3' : L5.u8_at RSEGS (mrestrict (ahid Awi md3) M3) (F / 8 + 2147450880 + 8) 1).
  { replace (F / 8 + 2147450880 + 8) with (F / 8 + 2147450888) by (clear; lia). rewrite HID3, VIS3. exact SHB3. }

  apply (call_read (F + 64) 1 0xb61c8 8 1 fx3 R3 M3 md3 LKi Awi cri si smi ei X1 MID3 PMORE PDONE ltac:(unfold X1; cbn [s_pos w_pos]; clear - PPOS LE1; lia)
           Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12 ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SHB3' ltac:(right; clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 d RP4 Z10 Hd SHORT LE BYT MID4.
  change (s_pos X1) with (s_pos X + 1) in SHORT, LE, BYT, MID4.
  set (si4 := PMSPA.with_src si src4) in *.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
  pose proof MID4 as ((K2 & K8 & K9 & K18 & K19 & K20 & K21 & K24 & K25 & K26 & K34) & BI4 & CP4 & _).
  pose proof BI4 as (HH4 & AM4 & MRT4 & _). pose proof AM4 as (Mh4 & MI4).
  clear WSi ICi CSBi CUARi OWNv FDi FWi FSWi FLCi FLWi FLCci FLVi VFi VSi VSHi.
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  vis_amid BI4 H4 MV4.
  pose proof OWNv as (S8 & S16 & S24 & S32 & S40 & S48 & S56 & S64 & S72 & S80 & S88 & S96).
  assert (S22 : getr R4 (reg 22) = Z_to_bv 64 (F + 64)) by (rewrite (R4c 22%nat) by inl; exact Y22).
  pose proof (PECGLW.gl_eval_u p (s_pos X) BOK ltac:(clear - LE1 PPOS; lia) TB) as GL.
  destruct (Z.eq_dec d 1) as [Ed|Nd].
  -
    subst d. replace (blen p <? s_pos X + 1 + 1) with false in GL by (symmetry; apply Z.ltb_ge; clear - LE; lia).
    assert (FD4 : L5.defined M4 (F + 64) 8) by (apply (L5.defined_sub M4 F 256); [exact (proj1 (L5A.defined_vis H4 M4 F 256 VFi) FDi)| clear; lia| clear; lia]).
    destruct (PMCG.u64_of_defined RSEGS M4 (F + 64) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) FD4) as (x & Hx & U64).
    assert (U64v : L5.u64_at RSEGS MV4 (F + 64) x).
    { exact (proj2 (L5A.u64_at_vis H4 M4 (F + 64) x (L5A.avis_sub H4 F 256 (F + 64) 8 VFi ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GF1; lia) ltac:(clear - GF2; lia)) U64). }
    pose proof (PECRVD.slice_bytes p (s_pos X + 1) 1 BOK) as SLB.
    assert (SLEN : length (UbjRef.slice p (s_pos X + 1) 1) = 1%nat) by (pose proof (PECRVD.slice_length p (s_pos X + 1) 1 ltac:(clear - PPOS; lia) ltac:(clear; lia) LE); clear - H; lia).
    assert (LANE : forall i, (i < 1)%nat -> PECGLW.lane x i = nth i (UbjRef.slice p (s_pos X + 1) 1) 0).
    { intros i Hi. apply (PECGLW.lane_of_bytes RSEGS M4 (F + 64) x _ i ltac:(clear - GF1; lia) ltac:(clear - GF2; lia) Hx U64 BYT ltac:(rewrite SLEN; clear; lia) SLB ltac:(rewrite SLEN; exact Hi)). }
    set (b0 := PECGLW.lane x 0) in *. set (b1 := PECGLW.lane x 1) in *. set (b2 := PECGLW.lane x 2) in *. set (b3 := PECGLW.lane x 3) in *.
    set (b4 := PECGLW.lane x 4) in *. set (b5 := PECGLW.lane x 5) in *. set (b6 := PECGLW.lane x 6) in *. set (b7 := PECGLW.lane x 7) in *.
    pose proof (PECGLW.lane_range x 0) as B0'. pose proof (PECGLW.lane_range x 1) as B1'. pose proof (PECGLW.lane_range x 2) as B2'. pose proof (PECGLW.lane_range x 3) as B3'.
    pose proof (PECGLW.lane_range x 4) as B4'. pose proof (PECGLW.lane_range x 5) as B5'. pose proof (PECGLW.lane_range x 6) as B6'. pose proof (PECGLW.lane_range x 7) as B7'.
    fold b0 in B0'. fold b1 in B1'. fold b2 in B2'. fold b3 in B3'. fold b4 in B4'. fold b5 in B5'. fold b6 in B6'. fold b7 in B7'.
    pose proof (LANE 0%nat ltac:(clear; lia)) as L0. rewrite (PECGLW.nth_slice p (s_pos X + 1) 1 0) in L0 by (clear - PPOS LE; lia). fold b0 in L0.
    replace (s_pos X + 1 + Z.of_nat 0) with (s_pos X + 1) in L0 by (clear; lia).

    rewrite <- L0 in GL.

    pose proof (PEAGLWP.aglWU_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => x | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PW. cbn beta iota in PW.
    L5SAR.feed PW ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PW as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & E1 & E2 & E8 & E9 & E10 & E11 & E18 & E19 & E20 & E21 & E22 & E23 & E24 & E25 & E26 & FL0 & _).
    lazymatch type of E10 with getr _ _ = AX2.edenot ?EEv _ =>
      rewrite (PECGLW.val_U b0 b1 b2 b3 b4 b5 b6 b7 (conj B0' (conj B1' (conj B2' (conj B3' (conj B4' (conj B5' (conj B6' B7'))))))) EEv (AX2.EVar 50)
                 ltac:(cbn [AX2.edenot AX2.ev]; rewrite (L5.unsigned_lit x Hx); symmetry; exact (PECGLW.xle_of_lanes x Hx))) in E10 end.
    apply (tail_R fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ _ fx5 R5 M5v 0xb61c8 MID4 GL MS5 MG5 FRZ5).
    + intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity.
    + intros j Hj; repeat (destruct Hj as [<-|Hj]; [match goal with H0 : getr R5 (reg _) = Z_to_bv 64 (bv_unsigned _) |- _ => rewrite H0; apply Z_to_bv_bv_unsigned end|]); destruct Hj.
    + exact E2.
    + exact E10.
    + exact FL0.
  -
    assert (DL : d = 0) by (clear - Hd Nd; lia). subst d.
    replace (blen p <? s_pos X + 1 + 1) with true in GL by (symmetry; apply Z.ltb_lt; clear - SHORT; lia).
    pose proof (PEAGLP2.aglNU_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => 0 | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PN. cbn beta iota in PN.
    L5SAR.feed PN ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | fail
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    destruct PN as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Y1' & Y10' & Y11').
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cri Aw4 M4 md4 fx4 fx5 R4 0xb61c8 R5 0xae310 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei (w_pos (s_pos X + 1 + 0) X)).
    { apply (amid_regs fx4 R4 M4 md4 LK4 Aw4 cri si4 sm4 ei _ fx5 R5 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec 0xb6444 1 fx5 R5 M4 md5 LK4 Aw4 cri si4 sm4 ei _ MID5 Y1' ltac:(split; [clear; lia| reflexivity]) Y10' Y11' ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z 0xb6444 fx7 R7 M7 md7 LK7 Aw7 cri si4 sm4 true _ zU_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
Qed.

Lemma arm_bad fxi Ri Mi mdi LKi Awi cri si smi ei tt :
  amid fxi Ri Mi mdi LKi Awi cri si smi ei (w_pos (s_pos X + 1) X) -> getr Ri (reg 10) = Z_to_bv 64 tt ->
  bat p (s_pos X) = tt -> s_pos X + 1 <= blen p -> 0 <= tt < 256 ->
  (0 <= tt <= 72 \/ 74 <= tt <= 75 \/ 77 <= tt <= 84 \/ 86 <= tt <= 104 \/ 106 <= tt <= 107 \/ 109 <= tt) ->
  srealizes RSEGS SCFG (PMSPA.cfg (fx:=fxi) RSEGS Ri 0xb6058 Mi mdi) K.
Proof.
  intros MID1 A0 TB LE1 Htt RG.
  entry_facts. frame_facts.
  destruct MP as (BOK & PPOS & PMORE & PDONE & PHALT & PBAD).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0f : 0 <= F < 2 ^ 64) by (clear - GF1 GF2; lia). assert (Q0g : 0 <= fl < 2 ^ 64) by (clear - GL1 GL2; lia).
  assert (Q0a : 0 <= sp < 2 ^ 64) by (clear - GSLO GSHI GSPT; lia). assert (Q0b : 0 <= op < 2 ^ 64) by (clear - O1 O3; lia).
  assert (Q0d : 0 <= oec < 2 ^ 64) by (clear - O1 O3 Eop Eoec; lia).
  pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as B8.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as B9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as B18.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 19))) as B19. pose proof (bv_unsigned_in_range 64 (getr R (reg 20))) as B20.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 21))) as B21. pose proof (bv_unsigned_in_range 64 (getr R (reg 22))) as B22.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 23))) as B23. pose proof (bv_unsigned_in_range 64 (getr R (reg 24))) as B24.
  pose proof (bv_unsigned_in_range 64 (getr R (reg 25))) as B25. pose proof (bv_unsigned_in_range 64 (getr R (reg 26))) as B26.
  change (bv_modulus 64) with (2 ^ 64) in B1, B8, B9, B18, B19, B20, B21, B22, B23, B24, B25, B26.
  set (X1 := w_pos (s_pos X + 1) X) in *.
  pose proof MID1 as ((J2 & J8 & J9 & J18 & J19 & J20 & J21 & J24 & J25 & J26 & J34) & BI1 & _).
  pose proof BI1 as (HH1 & AM1 & MRT1 & _).
  set (H1 := ahid Awi mdi) in *. set (MV1 := mrestrict H1 Mi) in *.
  vis_amid BI1 H1 MV1.
  pose proof AM1 as (Mh1 & MI1).
  pose proof (PECGLW.gl_none_type p (s_pos X) ltac:(clear - LE1; lia) ltac:(rewrite TB; apply PECGLW.int_width_0; exact RG)) as GL.
  assert (Htt' : 0 <= tt < 2 ^ 64) by (clear - Htt; lia).
  assert (STEPD : exists (fx3 : FPState) R3 M3v, (forall i : Z, 0 <= i < 2 ^ 64 -> M3v (Z_to_bv 64 i) = MV1 (Z_to_bv 64 i))
      /\ msteps RSEGS (@mkst fxi Ri (Z_to_bv 64 0xb6058) MV1 (seg_rom RSEGS)) (@mkst fx3 R3 (Z_to_bv 64 0xae310) M3v (seg_rom RSEGS))
      /\ (forall x, In x [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat -> getr R3 (reg x) = getr Ri (reg x))
      /\ getr R3 (reg 1) = Z_to_bv 64 0xb6274 /\ getr R3 (reg 10) = Z_to_bv 64 oec /\ getr R3 (reg 11) = Z_to_bv 64 5).
  { destruct RG as [RG|[RG|[RG|[RG|[RG|RG]]]]];
      [ pose proof (PEAGLP1.aglTd1_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => tt | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT
      | pose proof (PEAGLP1.aglTd2_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => tt | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT
      | pose proof (PEAGLP1.aglTd3_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => tt | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT
      | pose proof (PEAGLP1.aglTd4_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => tt | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT
      | pose proof (PEAGLP1.aglTd5_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => tt | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT
      | pose proof (PEAGLP1.aglTd6_conc fxi Ri MV1 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | 49%nat => tt | 50%nat => 0 | 64%nat => bv_unsigned (getr R (reg 1)) | 65%nat => bv_unsigned (getr R (reg 8)) | 66%nat => bv_unsigned (getr R (reg 9)) | 67%nat => bv_unsigned (getr R (reg 18)) | 68%nat => bv_unsigned (getr R (reg 19)) | 69%nat => bv_unsigned (getr R (reg 20)) | 70%nat => bv_unsigned (getr R (reg 21)) | 71%nat => bv_unsigned (getr R (reg 22)) | 72%nat => bv_unsigned (getr R (reg 23)) | 73%nat => bv_unsigned (getr R (reg 24)) | 74%nat => bv_unsigned (getr R (reg 25)) | 75%nat => bv_unsigned (getr R (reg 26)) | _ => 0 end)) as PT ].
    all: cbn beta iota in PT.
    all: L5SAR.feed PT ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | unfold PEAGLP2.aligned; assumption | unfold PEAGLWP.aligned; assumption | clear - Htt RG; lia
                           | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL GSLO; lia | clear - GL4 GSLO; lia | clear - GSLO GSHI GSPT; lia]).
    all: destruct PT as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11).
    all: exists fx3, R3, M3v; split; [exact FRZ3|]; split; [exact MS3|]; split; [| split; [exact Y1| split; [exact Y10| exact Y11]]].
    all: intros j Hj; apply KS3; revert j Hj; apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat); vm_compute; reflexivity. }
  destruct STEPD as (fx3 & R3 & M3v & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11).
  assert (E3v : M3v = MV1) by (apply L5SAR.mem_eq_of_agree; exact FRZ3). subst M3v.
  apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LKi cri Awi Mi mdi fxi fx3 Ri 0xb6058 R3 0xae310 MV1 K HH1 AM1 MS3 (fun x Hx => Hx) (fun a Ha => eq_refl)).
  intros M3 md3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3.
  assert (E3 : M3 = Mi) by (apply L5SAR.mem_eq_of_agree; exact FR3). subst M3.
  assert (MID3 : amid fx3 R3 Mi md3 LKi Awi cri si smi ei X1).
  { apply (amid_regs fxi Ri Mi mdi LKi Awi cri si smi ei X1 fx3 R3 md3 MID1 KS3 HH3 AM3 MRT3). }
  apply (call_mkec 0xb6274 5 fx3 R3 Mi md3 LKi Awi cri si smi ei X1 MID3 Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 ltac:(clear; lia)).
  intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
  apply (tail_Z 0xb6274 fx7 R7 M7 md7 LK7 Aw7 cri si smi true _ zD_run MID7 eq_refl); [| exact GL].
  unfold PECRVD.but_pos, X1. cbn. repeat split; reflexivity.
Qed.
End Frame.

Theorem get_length_call : srealizes RSEGS SCFG (PMSPA.cfg (fx:=fx) RSEGS R (pa_get_length AD) M model) K.
Proof.
  entry_facts.
  pose proof AM as (Mh & MI).
  pose proof A10 as X10. pose proof A11 as X11. rewrite L5K.rl10 in X10. rewrite L5K.rl11 in X11. fold op in X10. fold oec in X11.
  pose proof CPRE as (PA & IA & EA & VREF & SKA & BASE & ERR & TBOK & CONT & CL & ECS & ECI & ACCR).
  destruct MP as (BOK & PPOS & PMORE & PDONE & PHALT & PBAD).
  pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
  set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
  set (LB := PEC.owned s en k ++ LBX) in *.
  assert (BRB : forall x, In x LB -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47) by exact (PMASK.brb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
  assert (INCX : incl LBX LB) by (unfold LB; apply incl_appr; apply incl_refl).
  assert (BASE' : PMSTA.base_okA RSEGS PMA.AD M) by exact BASE.
  pose proof (PMASK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE') as (IC0 & CSBv & CUARv). fold H in IC0, CSBv, CUARv. fold MV in IC0, CSBv, CUARv.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 22528 128 HH ASTK ltac:(lia)) as (SL128 & SH128 & SWR). fold H in SWR. fold MV in SWR.

  pose proof (PEAGLP1.aglA_conc fx R MV (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | clear - SL128 SHI SPT; lia | clear - O1 O3; lia | clear - O1 O3 Eop Eoec; lia]).
  destruct PP as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & T1 & T2 & T8 & T9 & T10 & _ & _ & T19 & T20 & T26
                 & C96 & C88 & C80 & C72 & C64 & C56 & C48 & C40 & C32 & C24 & C16 & C8 & C128).
  unfold PMSPA.cfg. cbn [pa_get_length AD PeCLayoutA.CADDR_A].
  apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx1 R 0xb5f04 R1 0x5e718 M1v (fun a => sp - 128 <= a < sp - 128 + 128) K HH AM MS1 MG1).
  { intros a Ha N. apply FRZ1; [exact Ha| exact N]. }
  { intros a Ha Wa. split; [|intros X'; clear - X' Wa SLO SPT; lia]. unfold aclientw, aclient_g. right; left. split; [clear - Wa SL128 SHI SPT; lia| intros X'; clear - X'; lia]. }
  intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
  assert (NCS0 : forall a, sp - 128 <= a < sp -> ~ aclient L ar LB FF sp 22528 a).
  { intros a Xa Hc. destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 22528 a HH SPT Hc) as [Y'|Y'].
    - clear - Xa Y'; lia.
    - clear - Xa Y' SL128; lia. }
  assert (EK01f : L5SAR.ek L ar LB FF sp 22528 [] M M1).
  { apply (L5SAR.ek_piece L ar LB FF sp 22528 [] M M1 (fun a => sp - 128 <= a < sp - 128 + 128) FR1). intros a Ha Hc _ X'. apply (NCS0 a); [clear - X'; lia| exact Hc]. }
  assert (DK01f : L5SAR.dk L ar LB FF sp 22528 M M1) by (apply L5SAR.dk_grows; exact MGM1).
  pose proof (PMKA.ek_sublb L ar LB LBX FF sp 22528 [] M M1 INCX EK01f) as EK01.
  pose proof (PMKA.dk_sublb L ar LB LBX FF sp 22528 M M1 INCX DK01f) as DK01.
  assert (SV1 : forall a v, sp - 128 <= a -> a + 8 <= sp -> L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
  { intros a v Ha1 Ha2 X'. apply (proj1 (L5A.u64_at_vis H M1 a v (VIS a 8 ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia)) ltac:(clear - Ha1 SL128 SPT; lia) ltac:(clear - Ha2 SHI SPT; lia))).
    rewrite VIS1. exact X'. }
  assert (OWN1 : own sp R M1).
  { unfold own. split; [apply SV1; [clear; lia| clear; lia| exact C8]|]. split; [apply SV1; [clear; lia| clear; lia| exact C16]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C24]|]. split; [apply SV1; [clear; lia| clear; lia| exact C32]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C40]|]. split; [apply SV1; [clear; lia| clear; lia| exact C48]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C56]|]. split; [apply SV1; [clear; lia| clear; lia| exact C64]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C72]|]. split; [apply SV1; [clear; lia| clear; lia| exact C80]|].
    split; [apply SV1; [clear; lia| clear; lia| exact C88]|]. apply SV1; [clear; lia| clear; lia| exact C96]. }
  clear C96 C88 C80 C72 C64 C56 C48 C40 C32 C24 C16 C8 C128 SV1.

  assert (FRk2 : ff_room 2 FF LK) by (pose proof (FRM 2 ltac:(right; right; left; reflexivity)) as X'; unfold ff_room; clear - X'; lia).
  change 0x5e718 with (PMA.SM_PC 2).
  apply (PMAUAR.uar_sm L ar C HI LY HIok 2 LBX (PEC.owned s en k) FF LK cr Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R)
           fx1 R1 M M1 model model1 K 0xb5f74 ltac:(right; right; left; reflexivity) HH HH1 AM1 K0 ASTK MGM1 EK01 DK01).
  { rewrite L5K.rl2. exact T2. }
  { rewrite L5K.rl4. rewrite (KS1 4%nat) by inl. rewrite <- L5K.rl4. exact Rtp. }
  { rewrite L5K.rl1. exact T1. }
  { reflexivity. }
  { clear; lia. }
  { replace (sp - 128) with (sp + (-8) * 16) by (clear; lia). rewrite Z_mod_plus_full. exact A16. }
  { clear; lia. } { clear; lia. } { clear; lia. } { clear; lia. }
  { intros a Ha. exact Ha. }
  { intros Ma Mb OW AG. apply (own_agree sp R Ma Mb ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OW AG). }
  { exact FRk2. }
  { intros f Hf. specialize (FRS f Hf). clear - FRS; lia. }
  intros R2 M2 model2 F fl LK2 G G10 RP2 AM2 MRT2 ASTK2 EK02 DK02 EK12f DK12f AGF FW FSHW FSHZ FLC FLW FDEF VF VSH VFL APART.
  change (ff_bytes 2) with 256 in FW, FSHW, FSHZ, FLC, FLW, FDEF, VF, VSH, APART. change (256 / 8) with 32 in FSHW, FSHZ, VSH, APART.
  fold LB in EK12f, DK12f, APART.
  pose proof G as G'. destruct G' as [_ GSPT GSLO GSHI _ _ _ GFS1 GFS2 GFCEIL GLKI2 GFLP GFLNC GHH2 GFLC GFR GF8 GFBIG GF32 GFLA GFLR GFLBIG GNCF GNCS].
  change (ff_bytes 2) with 256 in GFS2, GFCEIL, GFLC, GFR, GF8, GFBIG, GFLA, GNCF. unfold FS_BYTES in GFS2, GFLP.

  pose proof (L5SAR.ek_trans L ar LB FF sp 22528 [] M M1 M2 EK01f EK12f) as EK02f.
  pose proof (L5SAR.dk_trans L ar LB FF sp 22528 M M1 M2 DK01f DK12f) as DK02f.
  assert (HH2 : ri_inv HI LB ((F, 2, sp - 128 + 32) :: FF) LK2 cr Aw M2 (vml_of model2)) by exact GHH2.
  set (FF' := (F, 2, sp - 128 + 32) :: FF) in *.
  set (H2 := ahid Aw model2) in *. set (MV2 := mrestrict H2 M2) in *.
  pose proof (PMASK.stk_vis L ar C HI LY HIok _ _ LK2 cr Aw M2 model2 sp 22528 128 HH2 ASTK2 ltac:(lia)) as (_ & _ & SWR2). fold H2 in SWR2. fold MV2 in SWR2.

  assert (R2c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R2 (reg j) = getr R1 (reg j)).
  { intros j Hj. apply (L5SAR.cs_of_preserved R1 R2 j RP2 Hj). }
  assert (B2R : getr R2 (reg 2) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 2%nat) by inl; exact T2).
  assert (B8R : getr R2 (reg 8) = Z_to_bv 64 sp) by (rewrite (R2c 8%nat) by inl; exact T8).
  assert (B9R : getr R2 (reg 9) = Z_to_bv 64 (sp - 128)) by (rewrite (R2c 9%nat) by inl; exact T9).
  assert (B19R : getr R2 (reg 19) = Z_to_bv 64 op) by (rewrite (R2c 19%nat) by inl; exact T19).
  assert (B20R : getr R2 (reg 20) = Z_to_bv 64 oec) by (rewrite (R2c 20%nat) by inl; exact T20).
  assert (B26R : getr R2 (reg 26) = Z_to_bv 64 2147450880) by (rewrite (R2c 26%nat) by inl; exact T26).
  assert (B10R : getr R2 (reg 10) = Z_to_bv 64 F) by (rewrite <- L5K.rl10; exact G10).
  assert (FLCv : L5.u64_at RSEGS MV2 (F + 248) fl) by (replace (F + 248) with (F + 256 - 8) by (clear; lia); exact FLC).
  pose proof GFR as (GF1 & GF2 & _). pose proof GFLR as (GL1 & GL2 & GL3 & GL4).
  assert (Q0 : 0 <= sp < 2 ^ 64 /\ 0 <= op < 2 ^ 64 /\ 0 <= oec < 2 ^ 64 /\ 0 <= F < 2 ^ 64 /\ 0 <= fl < 2 ^ 64)
    by (clear - SL128 SHI SPT O1 O3 Eop Eoec GFR GFLR; lia).
  destruct Q0 as (Q0a & Q0b & Q0d & Q0f & Q0g).
  pose proof (PEAGLP1.aglB_conc fx1 R2 MV2 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | 48%nat => fl | _ => 0 end)) as PP.
  cbn beta iota in PP.
  L5SAR.feed PP ltac:(first [assumption | unfold PEAGLP1.aligned; assumption | clear - SL128 SHI SPT; lia | clear - GFR; lia | clear - GFLR; lia | clear - GFCEIL SL128 GSLO; lia | clear - GL4 SL128 GSLO; lia]).
  destruct PP as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & Y1 & Y10 & Y11 & Y12 & _ & _ & _ & Y18 & Y21 & Y22 & Y24 & Y25
                 & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & SH4 & _).
  set (W3 := fun a => (sp - 104 <= a < sp - 104 + 8) \/ (F <= a < F + 24) \/ (F / 8 + 2147450880 <= a < F / 8 + 2147450880 + 20)).
  apply (L5SAR.apiece L ar C HI LYa HIok LB FF' LK2 cr Aw M2 model2 fx1 fx3 R2 0xb5f74 R3 (pa_src_read AD) M3v W3 K HH2 AM2 MS3 MG3).
  { intros a Ha Hn. apply FRZ3; [exact Ha| intros X'; apply Hn; left; clear - X'; lia| intros X'; apply Hn; right; left; clear - X'; lia| intros X'; apply Hn; right; right; clear - X'; lia]. }
  { intros a Ha Wa. split.
    - destruct Wa as [X'|[X'|X']].
      + unfold aclientw, aclient_g. right; left. split; [clear - X' SL128 SHI SPT; lia| intros Y'; clear - Y'; lia].
      + apply (L5SAR.fframe_client L ar LB FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity| change (ff_bytes 2) with 256; clear - X'; lia].
      + apply (L5SAR.fframe_shadow_client L ar LB FF' 0 0 F 2 (sp - 128 + 32)); [left; reflexivity|]. change (ff_bytes 2) with 256.
        unfold in_shadow_of, S. rewrite (proj1 (proj2 GF8)). unfold SB. clear - X'; lia.
    - destruct Wa as [X'|[X'|X']]; clear - X' GFR SL128 SPT; lia. }
  intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3. change (mrestrict H2 M3 = M3v) in VIS3.
  assert (EK23f : L5SAR.ek L ar LB FF sp 22528 [] M2 M3).
  { apply (L5SAR.ek_piece L ar LB FF sp 22528 [] M2 M3 W3 FR3). intros a Ha Hc _ X'. destruct X' as [X'|[X'|X']].
    - apply (NCS0 a); [clear - X'; lia| exact Hc].
    - destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (Y' & _). clear - X' Y'; lia.
    - destruct (APART a 1 sp 22528 ltac:(intros i Hi; replace (a + i) with a by (clear - Hi; lia); exact Hc) ltac:(clear; lia)) as (_ & Y' & _). unfold SB in Y'. clear - X' Y'; lia. }
  pose proof (L5SAR.ek_trans L ar LB FF sp 22528 [] M M2 M3 EK02f EK23f) as EK03f.
  assert (DK23f : L5SAR.dk L ar LB FF sp 22528 M2 M3) by (apply L5SAR.dk_grows; exact MGM3).
  pose proof (L5SAR.dk_trans L ar LB FF sp 22528 M M2 M3 DK02f DK23f) as DK03f.
  assert (OWN3 : own sp R M3).
  { apply (own_agree sp R M1 M3 ltac:(clear - SL128 SPT; lia) ltac:(clear - SHI SPT; lia) OWN1). intros a Ha. unfold ocell in Ha.
    rewrite FR3; [apply AGF; clear - Ha; lia| clear - Ha SL128 SHI SPT; lia| intros [X'|[X'|X']]; clear - X' Ha GFCEIL GFR SL128 SPT GSLO; unfold SB in *; lia]. }
  assert (BI3 : PMAUK.binv L ar HI M model LBX FF LK Aw sp 22528 (sp - 128) (own sp R) F 2 WR (PEC.owned s en k) M3 model3 LK2 cr Aw).
  { unfold PMAUK.binv. split; [exact HH3|]. split; [exact AM3|].
    split; [eapply L5LZ.model_rt_trans; [exact MRT1| eapply L5LZ.model_rt_trans; [exact MRT2| exact MRT3]]|].
    split; [apply incl_refl|]. split; [exact GLKI2|]. split; [exact (L5SAR.astk_grows ar M2 M3 sp 22528 ASTK2 MGM3)|].
    split; [apply (L5SAR.ek_W L ar LBX FF sp 22528 WR [] M M3 (PMKA.ek_sublb L ar LB LBX FF sp 22528 [] M M3 INCX EK03f)); intros a _ r0 []|].
    split; [exact (PMKA.dk_sublb L ar LB LBX FF sp 22528 M M3 INCX DK03f)|].
    split; [exact OWN3|].
    change (ff_bytes 2 / 8) with 32. apply (L5.defined_grows M2 M3 _ _ MGM3).
    apply (proj1 (L5A.defined_vis H2 M2 (F / 8 + SB) 32 VSH)). intros i Hi. pose proof (FSHZ i Hi) as Z0. unfold MV2 in Z0. rewrite Z0. discriminate. }
  assert (AMID3 : amid F fx3 R3 M3 model3 LK2 Aw cr s sm e X).
  { unfold amid. split; [| split; [exact BI3| split; [| split; [| split; [intros X'; exact X'| split; [unfold PMSP.credit_keep; clear; lia| split; [reflexivity| split; [reflexivity| split; reflexivity]]]]]]]].
    - split; [rewrite (KS3 2%nat) by inl; exact B2R|]. split; [rewrite (KS3 8%nat) by inl; exact B8R|]. split; [rewrite (KS3 9%nat) by inl; exact B9R|].
      split; [exact Y18|]. split; [rewrite (KS3 19%nat) by inl; exact B19R|]. split; [rewrite (KS3 20%nat) by inl; exact B20R|].
      split; [exact Y21|]. split; [exact Y24|]. split; [exact Y25|]. split; [rewrite (KS3 26%nat) by inl; exact B26R|].
      intros j Hj. rewrite (KS3 j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
      rewrite (R2c j) by (revert j Hj; apply (L5K.incl_b [3; 4; 27]%nat); vm_compute; reflexivity).
      apply KS1. revert j Hj. apply (L5K.incl_b [3; 4; 27]%nat). vm_compute. reflexivity.
    - apply (cpre_keepA LB sp 22528 [] M M3 X s sm e EK03f PMKA.wapp_nil BRB); [unfold LB; apply incl_appl; apply incl_refl| unfold LB; apply incl_appr; exact INCS| intros i _ r0 []| intros a _ r0 []| intros q' m _ i _ r0 []| exact CPRE].
    - unfold PMSPA.src_step. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [intros X'; exact X'| clear; lia]. }
  assert (SH4' : L5.u8_at RSEGS (mrestrict (ahid Aw model3) M3) (F / 8 + 2147450880 + 4) 1).
  { replace (F / 8 + 2147450880 + 4) with (F / 8 + 2147450884) by (clear; lia). rewrite HID3. fold H2. rewrite VIS3. exact SH4. }
  clear FR3 W3 FRZ3 MS3 OWN3 OWN1 EK23f DK23f.

  apply (call_read F fl LK2 M2 model2 G APART (F + 32) 1 0xb6050 4 1 fx3 R3 M3 model3 LK2 Aw cr s sm e X AMID3 PMORE PDONE PPOS Y1 ltac:(split; [clear; lia| reflexivity]) Y10 Y11 Y12
           ltac:(clear; lia) ltac:(clear; lia) ltac:(clear; lia) SH4' ltac:(right; clear; lia)).
  intros fx4 R4 M4 md4 LK4 Aw4 src4 sm4 d RP4 Z10 Hd SHORT LE BYT MID4.
  set (s4 := PMSPA.with_src s src4) in *.
  assert (R4c : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R4 (reg j) = getr R3 (reg j))
    by (intros j Hj; exact (L5SAR.cs_of_preserved R3 R4 j RP4 Hj)).
  assert (G22 : getr R4 (reg 22) = Z_to_bv 64 (F + 32)) by (rewrite (R4c 22%nat) by inl; exact Y22).
  pose proof MID4 as ((K2 & K8 & K9 & K18 & K19 & K20 & K21 & K24 & K25 & K26 & K34) & BI4 & CP4 & _).
  pose proof BI4 as (HH4 & AM4 & MRT4 & _). pose proof AM4 as (Mh4 & MI4).
  set (H4 := ahid Aw4 md4) in *. set (MV4 := mrestrict H4 M4) in *.
  pose proof (PMAUK.vis_facts L ar C HI LYa HIok M model LBX FF LK Aw sp 22528 (sp - 128) (sp - 96) sp (ocell sp) (own sp R) F fl 2 LK2 M2 model2 cr (PEC.owned s en k) G
                WR _ _ _ _ _ _ BI4) as (_ & _ & (FD4 & _) & (_ & _ & VF4 & _)).
  change (ff_bytes 2) with 256 in FD4, VF4. fold H4 in FD4, VF4. fold MV4 in FD4.
  destruct (Z.eq_dec d 1) as [Ed|Nd].
  -
    rewrite Ed in Z10, BYT, MID4, SHORT, LE. clear Hd Ed.
    rewrite (slice_pos_1 p (s_pos X)) in BYT by (clear - PPOS LE; lia).
    assert (U8 : L5.u8_at RSEGS M4 (F + 32) (bat p (s_pos X))) by (specialize (BYT 0%nat ltac:(cbn; clear; lia)); cbn [nth] in BYT; rewrite Z.add_0_r in BYT; exact BYT).
    pose proof (bat_byte p (s_pos X) BOK ltac:(clear - LE PPOS; lia)) as BB.
    set (t := bat p (s_pos X)) in *.
    pose proof (PEAGLP1.aglB1_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | _ => 0 end)) as PP.
    cbn beta iota in PP. L5SAR.feed PP ltac:(first [assumption]).
    destruct PP as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    assert (DV4 : L5.defined MV4 (F + 32) 1) by (apply (L5.defined_sub MV4 F 256); [exact FD4| clear; lia| clear; lia]).
    assert (U8v : L5.u8_at RSEGS MV4 (F + 32) t).
    { apply (proj2 (L5A.u8_at_vis H4 M4 (F + 32) t (L5A.avis_sub H4 F 256 (F + 32) 1 VF4 ltac:(clear; lia) ltac:(clear; lia)) ltac:(clear - GFR; lia) ltac:(clear - GFR; lia))). exact U8. }
    destruct (PMPX.lbu_run RSEGS fx5 R5 MV4 0xb6054 W_b6004 10%bv 22%bv 0%bv (F + 32) F_b6004 eq_refl D_b6004) as (tb & Htb & U8t & MSt).
    { intros E0. apply (f_equal bv_unsigned) in E0. vm_compute in E0. discriminate E0. }
    { clear; lia. } { clear; lia. }
    { rewrite L5K.rl22. rewrite (KS5 22%nat) by inl. exact G22. }
    { clear - Q0f GFR; lia. }
    { change (bv_signed (0%bv : bv 12)) with 0. clear - Q0f GFR; lia. }
    { change (bv_signed (0%bv : bv 12)) with 0. rewrite Z.add_0_r. exact DV4. }
    change (0xb6054 + 4) with 0xb6058 in MSt. rewrite L5K.rl10 in MSt. change (bv_signed (0%bv : bv 12)) with 0 in U8t. rewrite Z.add_0_r in U8t.
    assert (Etb : tb = t) by exact (u8_at_inj MV4 (F + 32) tb t U8t U8v Htb BB). subst tb.
    set (R5' := regupd R5 (reg 10) (Z_to_bv 64 t)) in MSt.
    assert (R5o : forall j, In j [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R5' (reg j) = getr R4 (reg j)).
    { intros j Hj. unfold R5'. rewrite (reg10_other R5 _ j Hj). apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    assert (R510 : getr R5' (reg 10) = Z_to_bv 64 t) by (unfold R5'; apply PMPX.regupd_same_idx; lia).
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 md4 fx4 fx5 R4 0xb6050 R5' 0xb6058 MV4 K HH4 AM4 (msteps_trans _ _ _ _ MS5 MSt) (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid F fx5 R5' M4 md5 LK4 Aw4 cr s4 sm4 e (w_pos (s_pos X + 1) X)).
    { apply (amid_regs F fx4 R4 M4 md4 LK4 Aw4 cr s4 sm4 e _ fx5 R5' md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply R5o. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    clearbody R5'.

    destruct (Z.eq_dec t 85) as [E85|N85]; [rewrite E85 in R510; exact (arm_U F fl LK2 M2 model2 G APART fx5 R5' M4 md5 LK4 Aw4 cr s4 sm4 e MID5 R510 E85 LE)|].
    destruct (Z.eq_dec t 105) as [E105|N105]; [rewrite E105 in R510; exact (arm_i F fl LK2 M2 model2 G APART fx5 R5' M4 md5 LK4 Aw4 cr s4 sm4 e MID5 R510 E105 LE)|].
    destruct (Z.eq_dec t 73) as [E73|N73]; [rewrite E73 in R510; exact (arm_I F fl LK2 M2 model2 G APART fx5 R5' M4 md5 LK4 Aw4 cr s4 sm4 e MID5 R510 E73 LE)|].
    destruct (Z.eq_dec t 108) as [E108|N108]; [rewrite E108 in R510; exact (arm_l F fl LK2 M2 model2 G APART fx5 R5' M4 md5 LK4 Aw4 cr s4 sm4 e MID5 R510 E108 LE)|].
    destruct (Z.eq_dec t 76) as [E76|N76]; [rewrite E76 in R510; exact (arm_L F fl LK2 M2 model2 G APART fx5 R5' M4 md5 LK4 Aw4 cr s4 sm4 e MID5 R510 E76 LE)|].
    apply (arm_bad F fl LK2 M2 model2 G APART fx5 R5' M4 md5 LK4 Aw4 cr s4 sm4 e t MID5 R510 eq_refl LE BB). clear - BB N85 N105 N73 N108 N76. lia.
  -
    assert (D0 : d = 0) by (clear - Hd Nd; lia). rewrite D0 in Z10, SHORT, MID4. clear Hd Nd.
    pose proof (PECGLW.gl_none_end p (s_pos X) ltac:(clear - SHORT; lia)) as GL.
    pose proof (PEAGLP1.aglE0_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 36%nat => op | 38%nat => oec | 47%nat => F | _ => 0 end)) as PP.
    cbn beta iota in PP. L5SAR.feed PP ltac:(first [assumption]).
    destruct PP as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & Z1 & Z10' & Z11).
    assert (E5 : M5v = MV4) by (apply L5SAR.mem_eq_of_agree; intros a Ha; apply FRZ5; exact Ha). subst M5v.
    apply (L5SAR.apiece_ro L ar C HI LYa HIok _ FF' LK4 cr Aw4 M4 md4 fx4 fx5 R4 0xb6050 R5 0xae310 MV4 K HH4 AM4 MS5 (fun x Hx => Hx) (fun a Ha => eq_refl)).
    intros M5 md5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5.
    assert (E5 : M5 = M4) by (apply L5SAR.mem_eq_of_agree; exact FR5). subst M5.
    assert (MID5 : amid F fx5 R5 M4 md5 LK4 Aw4 cr s4 sm4 e (w_pos (s_pos X + 0) X)).
    { apply (amid_regs F fx4 R4 M4 md4 LK4 Aw4 cr s4 sm4 e _ fx5 R5 md5 MID4); [| exact HH5| exact AM5| exact MRT5].
      intros j Hj. apply KS5. revert j Hj. apply (L5K.incl_b [2; 3; 4; 8; 9; 18; 19; 20; 21; 24; 25; 26; 27]%nat). vm_compute. reflexivity. }
    apply (call_mkec F fl LK2 M2 model2 G 0xb60e4 1 fx5 R5 M4 md5 LK4 Aw4 cr s4 sm4 e _ MID5 Z1 ltac:(split; [clear; lia| reflexivity]) Z10' Z11 ltac:(clear; lia)).
    intros fx7 R7 M7 md7 LK7 Aw7 RP7 MID7.
    apply (tail_Z F fl LK2 M2 model2 G APART 0xb60e4 fx7 R7 M7 md7 LK7 Aw7 cr s4 sm4 true _ zT_run MID7 eq_refl); [| exact GL].
    unfold PECRVD.but_pos. cbn. repeat split; reflexivity.
Qed.

End Call.

Theorem get_length_ok : PECSA.get_length_spec L ar HI P.
Proof.
  unfold PECSA.get_length_spec, PECSPA.get_length_spec.
  intros PMODE fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 ARGS CPRE INCS POK MP CRED KONT.
  destruct ARGS as (A10 & A11).
  exact (get_length_call fx R M model K LBX FF LK Aw cr sp r fb cat p X s str sm en k e HH AM K0 ENT FRM FRS FOK SP32 A10 A11 CPRE INCS POK MP KONT).
Qed.
End WithHeap.
End PEACGL.
