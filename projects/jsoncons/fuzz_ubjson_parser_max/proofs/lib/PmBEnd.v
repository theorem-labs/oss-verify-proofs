(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA IcptIfaceAB0 L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsAB0 L5CoreAB0 L5StepARB0 PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAb PmModelFactsA PmStepAB0 PmStep PmParKit PmBSrcKit PmBParKit PmBReset1 PmSpecsBX PmBEndP.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require AsanUbsan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmBEnd () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Init.Peano."; "Corelib.Numbers.BinNums."; "LinuxProcessSemantics.Riscv.Prelude."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmBEnd.PMBEND."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmLayoutA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsA.PMSPA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsAb.PMB."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmSpecsBX.PMBX."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PropExec."; "OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M."; "Stdlib.ZArith.BinInt.Z."; "stdpp.bitvector.definitions."], [["1nat"; "2I"; "2and"; "2eq"; "2not"; "2or"; "3lt"; "4Z"; "0HI"; "0L"; "5bvmap"; "0R"; "0R'"; "6end_run"; "7AADDR_B"; "7ADDR_B"]; ["8args_end"; "8prog_pop"; "8run_spec"; "9end_array_spec"; "9end_object_spec"; ":ann_shrink_spec"; ";getr"; ";regupd"; ";v_srai"; "<loaded_segments"; "0SCFG_P"; "=add"; "=div"; "=le"; "=lt"; "=modulo"]; ["=of_nat"; "=pow"; "0ar"; "0d"; "0j"; "0pc0"; ">BV"; ">Z_to_bv"; ">bv"; ">bv_unsigned"; "0va"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.AsanUbsan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMBEND.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := AsanUbsan.M.loaded_segments.
Definition end_run (pc0 sh : Z) : Prop :=
forall (fx : FPState) (R : bvmap 5 word) (M : word -> option byte) (sp dp b sz op ov oec : Z),
0 <= sp < 2 ^ 64 -> 0 <= dp < 2 ^ 64 -> 0 <= b < 2 ^ 64 -> 0 <= sz < 2 ^ 64 -> 0 <= op < 2 ^ 64 -> 0 <= ov < 2 ^ 64 -> 0 <= oec < 2 ^ 64 ->
getr R (reg 2) = Z_to_bv 64 sp -> getr R (reg 10) = Z_to_bv 64 op -> getr R (reg 11) = Z_to_bv 64 ov -> getr R (reg 12) = Z_to_bv 64 oec ->
L5.img_clear M 65536 1269760 -> L5.u64_at RSEGS M 1296952 2147450880 -> L5.u32_at RSEGS M 1296960 1 -> 140735332487200 <= sp <= 140737488355328 ->
sp mod 16 = 0 -> L5.writable RSEGS M (sp - 32) 32 -> 6893568 <= op <= 140737488354944 -> op mod 8 = 0 ->
(2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) -> L5KA.zeros_at M ((op / 8) + 2147450880) 3 ->
L5KA.zeros_at M (((op + 32) / 8) + 2147450880) 44 -> L5KA.zeros_at M (((op + 20) / 8) + 2147450880) 1 ->
L5.writable RSEGS M op 384 -> ((sp - 32) + 32 <= op \/ op + 384 <= (sp - 32)) -> 6893568 <= ov <= 140737488355320 -> ov mod 8 = 0 ->
(2147446784 + 17592186048512 <= ov \/ ov + 8 <= 2147446784) -> L5KA.zeros_at M ((ov / 8) + 2147450880) 1 -> L5.writable RSEGS M ov 8 ->
((sp - 32) + 32 <= ov \/ ov + 8 <= (sp - 32)) ->
L5.u64_at RSEGS M ov 1238880 -> L5KA.zeros_at M sh 1 -> L5.u32_at RSEGS M (op + 12) dp -> L5.u8_at RSEGS M (op + 16) 0 ->
L5.u32_at RSEGS M (op + 20) 0 -> L5.u64_at RSEGS M (op + 360) b -> L5.u64_at RSEGS M (op + 368) (b + sz) -> 1 <= dp <= 1024 ->
4096 <= b <= 140737488289792 -> 64 <= sz <= 32800 -> sz mod 32 = 0 -> (op + 384 <= ov \/ ov + 8 <= op) ->
exists fx' R' M', mem_grows M M'
/\ (forall i, 0 <= i < 2 ^ 64 -> ~ (sp - 32 <= i < sp) -> ~ (op + 8 <= i < op + 9) -> ~ (op + 12 <= i < op + 16) -> ~ (op + 368 <= i < op + 376) ->
M' (Z_to_bv 64 i) = M (Z_to_bv 64 i))
/\ msteps RSEGS (@mkst fx R (Z_to_bv 64 pc0) M (seg_rom RSEGS)) (@mkst fx' R' (Z_to_bv 64 0xab054) M' (seg_rom RSEGS))
/\ (forall j, In j [3; 4; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R' (reg j) = getr R (reg j))
/\ getr R' (reg 1) = getr R (reg 1) /\ getr R' (reg 2) = Z_to_bv 64 sp /\ getr R' (reg 8) = getr R (reg 8) /\ getr R' (reg 9) = getr R (reg 9)
/\ getr R' (reg 10) = Z_to_bv 64 (op + 360) /\ getr R' (reg 11) = Z_to_bv 64 (sz / 32)
/\ L5.u8_at RSEGS M' (op + 8) 1 /\ L5.u32_at RSEGS M' (op + 12) (dp - 1) /\ L5.u64_at RSEGS M' (op + 368) (b + sz - 32).
Lemma srai_reg : ltac2:(TCodec.tc2 tcn__PmBEnd "R<&:y5'Q8yR0%211%5241'7'2&Mzr1%3221&N&Q1+2+QO%3221%5271%;271'3&Fr3&Q7&Q0u<%211%42I1%7261r2%72J1%;3J31&Gr4(Q6+<(1%33Q321&H%B262&Q9y6+5%93217%Q913/021%6251%9281%@3?;1%L2Q6F&L+Q0%22C1%N2QA1%Q23QA51'0&4%Q532Q>Q0%211&6uQ0%22Q01%Q61Q8%Q82QM1%Q;2O1r8%Q=213%Q?3QN31p071p0;1pR:?1%QO2A1tJR2H1p0Q:1p0QG1pR8R41pHR61").
Proof. intros R d.
intros Hd G R'. split.
- unfold R'. rewrite <- L5K.rl12. rewrite getr_same by (intros X; discriminate X). rewrite <- L5K.rl12 in G. rewrite G.
change (bv_unsigned (5%bv : bv 6)) with 5. apply PMBRS1.v_srai5_small. exact Hd.
- intros j Hj Hl. unfold R'. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (12%bv : bv 5)) with 12 in E.
rewrite Z.mod_small in E by lia. lia.
Qed.
Ltac run_tac A_conc B_conc :=
intros fx R M sp dp b sz op ov oec H1 H2 H3 H4 H5 H6 H7 G2 G10 G11 G12 K0 K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16 K17 K18 K19 K20 K21 K22
K23 K24 K25 K26 K27 K28 K29 K30 K31;
pose proof (A_conc fx R M (fun j => match j with 2%nat => sp | 33%nat => dp | 34%nat => b | 35%nat => sz | 36%nat => op | 37%nat => ov | 38%nat => oec | _ => 0 end)) as P;
cbn beta iota in P;
L5SAR.feed P ltac:(first [assumption | unfold PMBENP.aligned; assumption]);
destruct P as (fx1 & R1 & M1 & MG1 & _ & FRZ1 & MS1 & KS1 & T2 & T10 & T11 & T12 & T13 & T14 & T15 & T16 & T17 & S8 & C8 & C12 & S24 & S16);
pose proof (PMBRS1.srai_to fx1 R1 M1 0xb1198 (ltac:(oW' 0xb1198%Z)) _ _ _ (ltac:(oF' 0xb1198%Z)) eq_refl (ltac:(oD' 0xb1198%Z)) eq_refl ltac:(lia) ltac:(lia)) as MSR;
destruct (srai_reg R1 sz ltac:(lia) T12) as (T12' & TO);
set (R1t := regupd R1 12%bv (v_srai (getr R1 12%bv) (bv_unsigned (5%bv : bv 6)))) in MSR, T12', TO;
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as B1; change (bv_modulus 64) with (2 ^ 64) in B1;
pose proof (B_conc fx1 R1t M1 (fun j => match j with 2%nat => sp | 36%nat => op | 39%nat => sz / 32 | 40%nat => b + sz - 32
| 41%nat => bv_unsigned (getr R (reg 1)) | _ => 0 end)) as P;
cbn beta iota in P;
assert (U2 : getr R1t (reg 2) = Z_to_bv 64 (sp - 16)) by (rewrite (TO 2%nat) by lia; exact T2);
assert (U10 : getr R1t (reg 10) = Z_to_bv 64 (op + 360)) by (rewrite (TO 10%nat) by lia; exact T10);
assert (U11 : getr R1t (reg 11) = Z_to_bv 64 (b + sz - 32)) by (rewrite (TO 11%nat) by lia; exact T11);
assert (WS1 : L5.writable RSEGS M1 (sp - 32) 32) by exact (L5.writable_grows RSEGS M M1 (sp - 32) 32 MG1 K5);
assert (WO1 : L5.writable RSEGS M1 (op + 368) 8)
by (apply (L5.writable_grows RSEGS M M1 (op + 368) 8 MG1); apply (L5.writable_sub RSEGS M op 384); [exact K12| lia| lia]);
assert (Q39 : 0 <= sz / 32 < 2 ^ 64) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]);
L5SAR.feed P ltac:(first [assumption | unfold PMBENP.aligned; assumption | lia]);
destruct P as (fx2 & R2 & M2 & MG2 & _ & FRZ2 & MS2 & KS2 & V1 & V2 & V11 & C368);
exists fx2, R2, M2;
split; [intros x Hx; apply MG2; apply MG1; exact Hx|];
split; [intros i Hi N1 N2 N3 N4; rewrite FRZ2 by (first [exact Hi| intros X; apply N4; lia]); apply FRZ1; [exact Hi| intros X; apply N1; lia| intros X; apply N2; lia| intros X; apply N3; lia]|];
split; [eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MSR| exact MS2]]|];
split; [intros j Hj; repeat (destruct Hj as [<-|Hj]; [rewrite (KS2 _) by inl; rewrite TO by lia; rewrite (KS1 _) by inl; reflexivity|]); destruct Hj|];
split; [rewrite V1; apply Z_to_bv_bv_unsigned|]; split; [exact V2|];
split; [rewrite (KS2 8%nat) by inl; rewrite TO by lia; rewrite (KS1 8%nat) by inl; reflexivity|];
split; [rewrite (KS2 9%nat) by inl; rewrite TO by lia; rewrite (KS1 9%nat) by inl; reflexivity|];
split; [rewrite (KS2 10%nat) by inl; exact U10|];
split; [exact V11|];
split; [apply (L5C.u8_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2; lia| lia| lia| exact C8]|];
split; [apply (PMF.u32_at_agree RSEGS M1 M2); [intros i Hi; apply FRZ2; lia| lia| lia| exact C12]| exact C368].
Lemma ea_run : ltac2:(TCodec.tc2 tcn__PmBEnd "4&=+eiQL+RPPSgW?%3221").
Proof. unfold end_run. run_tac PMBENP.aeaA_conc PMBENP.aepB_conc. Qed.
Lemma eo_run : ltac2:(TCodec.tc2 tcn__PmBEnd "4&=+fPe4+RPPSgWF%3221").
Proof. unfold end_run. run_tac PMBENP.aeoA_conc PMBENP.aepB_conc. Qed.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMB.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Variable IL : icpt_layout.
Hypothesis ICok : aicpt_ok L ar IL SCFG HI.
Hypothesis ILY : as0_icpt_layout IL.
Let LYa := PMB.ly_as0 L C LY.
Lemma end_core : ltac2:(TCodec.tc2 tcn__PmBEnd "R0'7&M+RPP0r1%3221'3&Or2+8%3221z%63;21&Kr3%2216+Vb\P0%?221'5r4%721;+T\[0%D221'2+T^Z0%G216+QWSe0%I271%5231+QWTl0%L21;%=231%>2:1&=r6&Lr5%221L+QoooPP0%J221%7261&EvJv9vQ2v8%544321&B&I&?&>r8+1&@%115&A%9;>876=<;5421p0;1p0B1p0K1p0Q;1p0QA1p0QI1pRFQN1pR<QO1").
Proof. intros pc0 va.
intros VA1 VA8 VA2 VAR RUN ASH. unfold PMSPA.run_spec, PMSPA.run_spec_r.
intros fx R M model K LBX FF LK Aw cr sp r fb cat s str sm e HH AM K0 ENT FRM FRS FOK SP32 ARGS RPRE INCS INV EC0 UNR CRED KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in *. change (14336 / 8) with 1792 in STKSH.
pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
destruct ARGS as ((A10 & A11 & A12) & HLEN).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10. rewrite L5K.rl11 in A11. rewrite L5K.rl12 in A12.
destruct RPRE as (PA & IA & VIS & VREF & BASE & ERR & TBOK).
pose proof FOK as ((rs & Hfb) & Fal).
pose proof (PMBPAR.op_vis L ar C HI LY HIok _ FF LK cr Aw M model fb _ s HH FOK PA) as ((O1 & O8 & ONSH) & Zop & Z32 & Z20 & OWR & OCE & OVIS & AOP & Eop).
pose proof (PMBPAR.ov_vis L ar C HI LY HIok _ FF LK cr Aw M model fb HH FOK VIS) as ((Q1 & Q8 & QNSH) & Zov & QWR & QCE & QVP & AOV & Eov).
pose proof (PMBSK.mach_vis L ar C HI LY HIok _ FF LK cr Aw M model HH BASE) as (VM0 & VM1 & VM2).
pose proof (PMBSK.stk_vis L ar C HI LY HIok _ FF LK cr Aw M model sp 14336 32 HH ASTK ltac:(lia)) as (SL32 & SH32 & SWR).
pose proof (PMBSK.img_shz_vis L ar C HI LY IL ICok ILY _ FF LK cr Aw M model va 1 HH VA1 ltac:(lia) VA8 ltac:(lia) ltac:(lia)) as ZSL.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & _ & _ & _ & _ & _ & STOP & _).
pose proof (WF _ Hfb) as (F1 & F2 & _). cbn [ff_addr ff_class fst snd] in F1, F2. change (ff_bytes 4) with 1024 in *. unfold app_mem, FS_BYTES in FSAPP, FSCEIL.
set (op := PMSPA.o_p PMB.AD fb) in *. set (ov := PMSPA.o_v PMB.AD fb) in *. set (oec := PMSPA.o_ec PMB.AD fb) in *.
assert (Eoec : oec = fb + 992) by reflexivity.
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n X1 X2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
destruct s as [mo dn dp src tb tg vb vk stk]. destruct src as [qc de rem].
cbn [PM.p_src PM.p_stk PM.p_depth PM.p_more PM.p_done PM.p_b PM.p_k PM.p_tb PM.p_tg PM.sr_qc] in *.
pose proof PA as (P0 & PD & PC0 & P8 & P9 & P12 & P16 & P20 & PNI & PSRC & P320 & P328 & PC320 & PTB & PVEC & PB1 & PB2 & PB3).
cbn [PM.p_src PM.p_stk PM.p_depth PM.p_more PM.p_done PM.p_b PM.p_k PM.p_tb PM.p_tg] in P12, PVEC, PTB.
pose proof PVEC as (VC0 & VC8 & VC16 & Hk & Hlen & Hal & DB & CB & AN & EL).
pose proof INV as (IM & ID & IDP & ISH & ITB). cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg] in IM, ID, IDP, ISH, ITB.
pose proof ISH as (SH1 & SH2 & _). unfold PM.MAX_DEPTH in SH2.
pose proof (PM.pow2_pos vk ltac:(lia)) as P2k.
assert (P2kh : 2 ^ vk <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in P2kh.
set (LB := PM.parser_own (PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) ++ LBX) in *.
set (LBc := (qc, 16384) :: PM.vs_own tb ++ LBX).
assert (EPO : LB = (qc, 16384) :: (vb, 32 * 2 ^ vk) :: PM.vs_own tb ++ LBX) by reflexivity.
assert (Ib : In (vb, 32 * 2 ^ vk) LB) by (rewrite EPO; right; left; reflexivity).
assert (Iq : In (qc, 16384) LBc) by (left; reflexivity).
assert (INCx : incl LBX LBc) by (intros x Hx; right; apply in_or_app; right; exact Hx).
assert (INCc : incl LBc LB) by (intros x Hx; rewrite EPO; destruct Hx as [<-|Hx]; [left; reflexivity| right; right; exact Hx]).
pose proof (WB _ Ib) as ((Bb0 & _ & Bb2 & _ & Bb4 & Bb5) & _). cbn [fst snd] in Bb0, Bb2, Bb4, Bb5.
destruct Bb5 as (_ & Bb5 & Bb6).
assert (BRB : forall x, In x LBc -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
{ intros x Hx. destruct (proj1 (WB x (INCc x Hx))) as (X0 & _ & _ & _ & _ & X5). clear - X0 X5. unfold app_mem in X5. lia. }
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47) by exact (PMBSK.frb_of L ar C HI HIok _ _ _ _ _ _ _ HH).
set (n := length stk) in *.
assert (HN : 2 <= Z.of_nat n <= 1025) by (clear - HLEN SH2; lia).
assert (CV : forall a m, op <= a -> a + m <= op + 384 -> L5A.avis H a m) by exact OVIS.
assert (U12 : L5.u32_at RSEGS MV (op + 12) dp) by (apply (proj2 (L5A.u32_at_vis H M (op + 12) dp (CV (op + 12) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P12).
assert (U16 : L5.u8_at RSEGS MV (op + 16) 0) by (apply (proj2 (L5A.u8_at_vis H M (op + 16) 0 (CV (op + 16) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P16).
assert (U20 : L5.u32_at RSEGS MV (op + 20) 0) by (apply (proj2 (L5A.u32_at_vis H M (op + 20) 0 (CV (op + 20) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact P20).
assert (U360 : L5.u64_at RSEGS MV (op + 360) vb) by (apply (proj2 (L5A.u64_at_vis H M (op + 360) vb (CV (op + 360) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact VC0).
assert (U368 : L5.u64_at RSEGS MV (op + 368) (vb + 32 * Z.of_nat n)).
{ replace (op + 368) with (op + 360 + 8) by lia. apply (proj2 (L5A.u64_at_vis H M (op + 360 + 8) _ (CV (op + 360 + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact VC8. }
assert (SZ32 : (32 * Z.of_nat n) mod 32 = 0) by (rewrite Z.mul_comm; apply Z_mod_mult).
destruct (RUN fx R MV sp dp vb (32 * Z.of_nat n) op ov oec) as (fx1 & R1 & M1v & MG1 & FRZ1 & MS1 & KS1 & G1 & G2 & G8 & G9 & G10 & G11 & C8 & C12 & C368);
[clear - SLO SHI SPT; lia| clear - IDP HN; lia| clear - Bb0 Bb4 SPT P2k; lia| clear - HN; lia| clear - O1; lia| clear - Q1; lia| clear - Eop Eoec O1; lia
|exact Rsp|exact A10|exact A11|exact A12|exact VM0|exact VM1|exact VM2|clear - SL32 SHI SPT; lia|exact A16|exact SWR|exact O1|exact O8|exact ONSH
|exact Zop|exact Z32|exact Z20|exact OWR|clear - OCE SL32; lia|exact Q1|exact Q8|exact QNSH|exact Zov|exact QWR|clear - QCE SL32; lia|exact QVP|exact ZSL
|exact U12|exact U16|exact U20|exact U360|exact U368|clear - IDP HN; lia|clear - Bb0 Bb4 SPT P2k; lia|clear - HN; lia|exact SZ32|clear - Eop Eov; lia|].
unfold PMSPA.cfg.
apply (L5SAR.apiece L ar C HI LYa HIok LB FF LK cr Aw M model fx fx1 R pc0 R1 0xab054 M1v
(fun a => (sp - 32 <= a < sp) \/ (op + 8 <= a < op + 9) \/ (op + 12 <= a < op + 16) \/ (op + 368 <= a < op + 376)) K HH AM MS1 MG1).
{ intros a Ha Hnw. apply FRZ1; [exact Ha| intros X; apply Hnw; left; exact X| intros X; apply Hnw; right; left; exact X| intros X; apply Hnw; right; right; left; exact X
| intros X; apply Hnw; right; right; right; exact X]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|[X|X]]]; unfold aclientw, aclient_g.
+ right; left. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
- destruct Wa as [X|[X|[X|X]]]; lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M1v) in VIS1.
assert (C8' : L5.u8_at RSEGS M1 (op + 8) 1).
{ apply (proj1 (L5A.u8_at_vis H M1 (op + 8) 1 (CV (op + 8) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact C8. }
assert (C12' : L5.u32_at RSEGS M1 (op + 12) (dp - 1)).
{ apply (proj1 (L5A.u32_at_vis H M1 (op + 12) (dp - 1) (CV (op + 12) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact C12. }
assert (C368' : L5.u64_at RSEGS M1 (op + 368) (vb + 32 * Z.of_nat n - 32)).
{ apply (proj1 (L5A.u64_at_vis H M1 (op + 368) _ (CV (op + 368) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1. exact C368. }
set (W1 := [(op + 8, 1); (op + 12, 4); (op + 368, 8)] : list L5.range).
assert (WAPP1 : PMKB.wapp W1).
{ unfold W1. repeat apply PMKB.wapp_cons; [..|apply PMKB.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; clear - ONSH; lia. }
assert (HHs : ri_inv HI (PM.vec_own vb vk ++ LBc) FF LK cr Aw M (vml_of model)).
{ rewrite EPO in HH. exact (PMBRS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH). }
assert (HH1s : ri_inv HI (PM.vec_own vb vk ++ LBc) FF LK cr Aw M1 (vml_of model1)).
{ rewrite EPO in HH1. exact (PMBRS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH1). }
assert (EK01 : L5SAR.ek L ar LBc FF sp 14336 W1 M M1).
{ apply (L5SAR.ek_piece L ar LBc FF sp 14336 W1 M M1 (fun a => (sp - 32 <= a < sp) \/ (op + 8 <= a < op + 9) \/ (op + 12 <= a < op + 16) \/ (op + 368 <= a < op + 376)) FR1).
intros a Ha Hc Ho [X|[X|[X|X]]].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 14336 a HHs SPT (L5SAR.aclient_appb L ar LBc (PM.vec_own vb vk) FF sp 14336 a Hc))
as [(_ & Z2)|Z2]; [apply Z2; clear - X; lia| clear - X Z2 SL32; lia].
- apply (Ho (op + 8, 1)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
- apply (Ho (op + 12, 4)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
- apply (Ho (op + 368, 8)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia]. }
assert (SHM1 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh M M1 a0 n0).
{ intros a0 n0 Ha Hn0 x Hx. pose proof (PMKB.S_in_shadow x ltac:(lia)) as SX. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX.
apply FR1; [clear - SX; lia| intros [Y|[Y|[Y|Y]]]; clear - Y SX SLO SPT ONSH; lia]. }
assert (AGB : L5C.agree_on M M1 vb (32 * 2 ^ vk)).
{ pose proof (WB _ Ib) as (_ & _ & _ & _ & _ & FAb & _).
destruct (FAb (fb, 4, rs) (in_or_app _ _ _ (or_introl Hfb))) as [FAb1|FAb1]; cbn [ff_addr ff_class fst snd] in FAb1; change (ff_bytes 4) with 1024 in FAb1; clear FAb.
all: intros i Hi; apply FR1; [clear - Hi Bb0 Bb4 SPT; lia| intros [Y|[Y|[Y|Y]]]; clear - Y Hi FAb1 Bb4 SL32 Eop; lia]. }
assert (ASTK0 : L5CA.astk ar M1 sp 12288).
{ pose proof (L5SAR.astk_sub ar M M1 sp 14336 0 12288 ASTK MGM1 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(rewrite Z.sub_0_r; exact A16)) as X.
rewrite Z.sub_0_r in X. exact X. }
assert (SZ0 : shadow_zero M (sp - 12288) 1536).
{ apply (PMKB.shadow_zero_sub M (sp - 14336) 1792); [| | clear; lia| clear; lia| clear; lia| exact STKSH].
+ apply PMKB.mod16_8'. replace (sp - 14336) with (sp + (-896) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
+ apply PMKB.mod16_8'. replace (sp - 12288) with (sp + (-768) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
assert (SZ1 : shadow_zero M1 (sp - 12288) 1536).
{ apply (PMKB.stksh_keepA L ar LBc FF sp 14336 W1 M M1 EK01 WAPP1 (sp - 12288) 1536); [clear - SLO SPT; lia| clear - SLO; lia| clear - SHI SPT; lia| | clear; lia| exact SZ0].
apply PMKB.mod16_8'. replace (sp - 12288) with (sp + (-768) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
unfold PMBX.ann_shrink_spec, PMSBX.ann_shrink_spec_at in ASH.
assert (LRM : length (removelast stk) = (n - 1)%nat) by (apply PMPK.removelast_len; clear - HLEN; lia).
apply (ASH fx1 R1 M1 model1 K LBc FF LK Aw cr (op + 360) vb vk (Z.of_nat n) (removelast stk) sp r HH1s AM1 K0).
{ split; [rewrite L5K.rl1; rewrite G1; exact Rra|]. split; [exact RAok|]. split; [rewrite L5K.rl2; exact G2|].
split; [rewrite L5K.rl3; rewrite (KS1 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (KS1 4%nat) by inl; exact Rtp|].
change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK0|]. change (12288 / 8) with 1536. exact SZ1. }
{ exact FRS. }
{ rewrite L5K.rl10. exact G10. }
{ rewrite L5K.rl11. rewrite G11. f_equal. rewrite Z.mul_comm. apply Z.div_mul. clear; lia. }
{ apply AOF; clear - Eop; lia. }
{ replace (op + 360) with (op + 45 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
{ apply (PMKB.acc_keepA' L ar LBc FF sp 14336 W1 M M1 EK01 WAPP1 FRB (op + 360) 24 (AOF (op + 360) 24 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
intros a Ha. apply PC320. clear - Ha; lia. }
{ rewrite LRM. clear - HLEN Hlen; lia. }
{ apply (PMKB.u64_keepA RSEGS L ar LBc FF sp 14336 W1 M M1 EK01 WAPP1 FRB (op + 360) vb (AOF (op + 360) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VC0].
intros i Hi r0 [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi; lia. }
{ rewrite LRM. replace (op + 360 + 8) with (op + 368) by lia. replace (vb + 32 * Z.of_nat (n - 1)) with (vb + 32 * Z.of_nat n - 32) by (clear - HLEN; lia). exact C368'. }
{ apply (PMKB.u64_keepA RSEGS L ar LBc FF sp 14336 W1 M M1 EK01 WAPP1 FRB (op + 360 + 16) _ (AOF (op + 360 + 16) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VC16].
intros i Hi r0 [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd]; clear - Hi; lia. }
{ clear - Hk; lia. }
{ exact Hal. }
{ intros i Hi. apply MGM1. apply DB. exact Hi. }
{ apply (PMFA.accA_agree M M1); [apply SHM1; clear - Bb0 Bb4 SPT Hlen P2k; lia| exact CB]. }
{ apply (PMFA.annA_agree M M1); [apply PMKB.mod16_8'; exact Hal| clear - Hlen P2k; lia| | apply SHM1; clear - Bb0 Bb4 SPT; lia| exact AN].
replace (32 * 2 ^ vk) with ((4 * 2 ^ vk) * 8) by lia. apply Z_mod_mult. }
{ intros i Hi. rewrite LRM in Hi. rewrite PMPK.nth_removelast_lt by (rewrite LRM; exact Hi).
assert (Hi' : Z.of_nat i < Z.of_nat n - 1) by (clear - Hi HLEN; lia).
apply (PMF.pstate_at_agree RSEGS M M1); [clear - Bb0; lia| clear - Hi' Bb4 SPT Hlen P2k; lia| | apply EL; clear - Hi HLEN; lia].
eapply (L5C.agree_on_sub M M1 vb (32 * 2 ^ vk)); [exact AGB| clear; lia| clear - Hi' Hlen P2k; lia]. }
intros fx2 R2 M2 model2 LK2 Aw2 RP2 VEC2 ACC2 HP2 MRT2 INCLK2 INCAw2 AM2 HH2.
change (PMSPA.pm_scr 0) with 12288 in HP2.
assert (EK12 : L5SAR.ek L ar LBc FF sp 14336 W1 M1 M2) by (apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 sp 12288 W1 [] M1 M2 HP2); [lia| lia| intros a _ _ r0 []]).
assert (EK12n : L5SAR.ek L ar LBc FF sp 14336 [] M1 M2) by (apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 sp 12288 [] [] M1 M2 HP2); [lia| lia| intros a _ _ r0 []]).
pose proof (L5SAR.ek_trans L ar LBc FF sp 14336 W1 M M1 M2 EK01 EK12) as EK02.
assert (DK02 : L5SAR.dk L ar LBc FF sp 14336 M M2).
{ apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M1 M2); [apply L5SAR.dk_grows; exact MGM1|].
apply (L5SAR.dk_callee L ar LBc [] FF [] sp 14336 sp 12288 [] M1 M2 HP2); lia. }
assert (ASTK2 : L5CA.astk ar M2 sp 14336) by (apply (PMKB.astk_after_ahpres L ar LBc FF M1 M2 sp 14336 sp 12288 [] (L5SAR.astk_grows ar M M1 sp 14336 ASTK MGM1) HP2); [clear; lia| clear; lia| clear; lia| exact STOP]).
assert (OUT1 : forall i, ~ (op + 8 <= i < op + 9) -> ~ (op + 12 <= i < op + 16) -> ~ (op + 368 <= i < op + 376) -> L5.outside W1 i).
{ intros i N1 N2 N3 r0 [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd]; lia. }
assert (OUTO : forall a m, PMSPA.aobjA FF a m -> (a + m <= op \/ op + 384 <= a) -> forall i, a <= i < a + m -> L5.outside W1 i).
{ intros a m _ X i Hi. apply OUT1; clear - X Hi; lia. }
assert (OUTB : forall q m, In (q, m) LBc -> forall i, q <= i < q + m -> L5.outside W1 i).
{ intros q m Hq i Hi. destruct (PMBSK.blk_obj_apart L ar C HI HIok _ _ _ _ _ _ _ q m op 384 HHs (in_or_app _ _ _ (or_intror Hq)) AOP) as [X|X];
apply OUT1; clear - X Hi; lia. }
assert (INS : incl (PM.vs_own str) LBc) by (intros x Hx; apply INCx; apply INCS; exact Hx).
assert (ITBc : forall c0 n0 p0, tb = PM.VLong c0 n0 p0 -> In (p0, c0) LBc) by (intros c0 n0 p0 E; right; apply in_or_app; left; rewrite E; left; reflexivity).
assert (OCLc : forall a, op <= a < op + 384 -> aclient L ar LBc FF sp 14336 a).
{ intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. split; [clear - Ha Eop; lia| intros X; clear - Ha Eop X; lia]. }
apply (KONT fx2 R2 M2 model2 LK2 Aw2 (PM.PST 1 dn (dp - 1) (PM.SRC qc de rem) tb tg vb vk (removelast stk)) sm e cr).
-
apply L5SAR.preserved_by_index. intros j Hj. pose proof Hj as Hj'. unfold L5SAR.cs_all in Hj.
rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2 Hj').
repeat (destruct Hj as [<-|Hj]; [first [rewrite G2; exact (eq_sym Rsp) | exact G8 | exact G9 | apply KS1; inl] |]). destruct Hj.
-
unfold PMSPA.run_post, PMSPA.run_pre.
split; [split; [|split; [|split; [|split; [|split; [|split]]]]]|split; [|split; [|right; split; [|split]]]].
+ apply (PMBPAR.parser_pop_updA M M2 op _ (PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk) PA); cbn [PM.p_stk PM.p_depth PM.p_src PM.p_b PM.p_k PM.p_tb PM.sr_qc].
* clear - O1; lia.
* clear - O1; lia.
* apply (PMKB.agA_obj L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB op 8 (AOF op 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
intros i Hi. apply OUT1; clear - Hi; lia.
* apply (PMKB.agA_obj L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB (op + 9) 3 (AOF (op + 9) 3 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
intros i Hi. apply OUT1; clear - Hi; lia.
* apply (PMKB.agA_obj L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB (op + 16) 344 (AOF (op + 16) 344 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))).
intros i Hi. apply OUT1; clear - Hi; lia.
* exact (PMKB.agsh_obj L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB op 384 AOP).
* intros i Hi. apply DK02; [clear - Hi O1; lia| apply OCLc; clear - Hi; lia| apply PD; exact Hi].
* apply (PMKB.u8_keepA RSEGS L ar LBc FF sp 14336 [] M1 M2 EK12n PMKB.wapp_nil FRB (op + 8) 1 (AOF (op + 8) 1 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)));
[intros i _ r0 []| exact C8'].
* apply (PMKB.u32_keepA RSEGS L ar LBc FF sp 14336 [] M1 M2 EK12n PMKB.wapp_nil FRB (op + 12) (dp - 1) (AOF (op + 12) 4 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia)));
[intros i _ r0 []| exact C12'].
* clear - IDP HN; lia.
* exact VEC2.
* destruct (BRB _ Iq) as (X1 & X2). cbn [fst snd] in X1, X2. clear - X1; lia.
* destruct (BRB _ Iq) as (X1 & X2). cbn [fst snd] in X1, X2. unfold PM.CHUNK. clear - X2; lia.
* apply (PMKB.agA_blk L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 BRB qc 16384 Iq). exact (OUTB qc 16384 Iq).
* intros c0 n0 p0 E. apply (PMKB.agA_blk L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 BRB p0 c0 (ITBc c0 n0 p0 E)). exact (OUTB p0 c0 (ITBc c0 n0 p0 E)).
+ apply (PMKB.iss_keepA RSEGS PMB.AD L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB BRB (PMSPA.o_is PMB.AD fb) str sm
(AOF (PMSPA.o_is PMB.AD fb) 272 ltac:(unfold PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_A]; clear; lia) ltac:(unfold PMSPA.o_is; cbn [pa_off_is PMB.AD ADDR_A]; clear; lia)) INS);
[| | exact IA].
* intros i Hi. apply OUT1; unfold PMSPA.o_is in Hi; cbn [pa_off_is PMB.AD ADDR_A] in Hi; clear - Hi Eop; lia.
* intros c0 n0 p0 E i Hi. subst str. exact (OUTB p0 c0 (INS (p0, c0) (or_introl eq_refl)) i Hi).
+ apply (PMKB.visitor_keepA RSEGS PMB.AD L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB ov AOV); [| exact VIS].
intros i Hi. apply OUT1; clear - Hi Eop Eov; lia.
+ apply (PMKB.u64_keepA RSEGS L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB (op + 384) ov (AOF (op + 384) 8 ltac:(clear - Eop; lia) ltac:(clear - Eop; lia))); [| exact VREF].
intros i Hi. apply OUT1; clear - Hi; lia.
+ apply (PMBSK.base_keep L ar C LY LBc FF sp 14336 W1 M M2 EK02); [| exact BASE]. intros a Ha. apply OUT1; clear - Ha O1; lia.
+ apply (PMKB.err_okA_keep RSEGS PMB.AD PMB.AAD L ar LBc FF sp 14336 W1 M M2 EK02 e PMB.addrs_wf_A); [| exact ERR].
intros a D. pose proof (PMBSK.dep_img a D) as DI. rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa). split; [clear - DI; lia|].
split; [exact (PMB.ly_static L C LY a D)|]. apply OUT1; clear - DI O1; lia.
+ exact TBOK.
+ unfold PMSPA.src_step. cbn [PM.p_src PM.sr_qc]. split; [reflexivity|]. split; [reflexivity|]. split; [clear; lia|]. split; [intros X; exact X| clear; lia].
+ intros X; exact X.
+ apply (PMKB.ec_keepA RSEGS L ar LBc FF sp 14336 W1 M M2 EK02 WAPP1 FRB oec 0 cat (AOF oec 16 ltac:(clear - Eoec; lia) ltac:(clear - Eoec; lia))); [| exact EC0].
intros i Hi. apply OUT1; clear - Hi Eop Eoec; lia.
+ unfold PM.inv. cbn [PM.p_more PM.p_done PM.p_depth PM.p_stk PM.p_tb PM.p_tg].
split; [reflexivity|]. split; [exact ID|]. split; [rewrite LRM; clear - IDP HLEN; lia|].
split; [apply (PMPK.stack_shape_pop stk ISH HLEN)| exact ITB].
+ unfold PMSPA.prog_pop. cbn [PM.p_stk PM.p_src]. split; [|reflexivity].
exists (last stk PM.ps_root). apply app_removelast_last. intros E. unfold n in HLEN. rewrite E in HLEN. cbn in HLEN. clear - HLEN; lia.
-
apply (L5SAR.ahpres_of L ar LBX FF sp 14336 _ M M2).
+ apply (L5SAR.ek_W L ar LBX FF sp 14336 _ W1 M M2 (PMKB.ek_sublb L ar LBc LBX FF sp 14336 W1 M M2 INCx EK02)).
intros a O r0 Hr X. unfold PMSPA.W_run, PMSPA.W_srcf, PMSPA.err_W, PMSPA.o_src, PMSPA.o_is, PMSPA.o_tb, PMSPA.o_vec in O.
fold op in O. fold oec in O. cbn [app] in O.
destruct Hr as [<-|[<-|[<-|[]]]]; unfold L5.in_rng in X; cbn [fst snd] in X.
* apply (O (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
* apply (O (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
* apply (O (op + 360, 24)); [do 5 right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; clear - X; lia].
+ pose proof ASTK2 as (_ & _ & _ & _ & D2 & _). exact D2.
+ exact (PMKB.dk_sublb L ar LBc LBX FF sp 14336 M M2 INCx DK02).
- change (PM.pot_parser (PMSPA.HV L ar) (PM.PST 1 dn (dp - 1) (PM.SRC qc de rem) tb tg vb vk (removelast stk)))
with (PM.pot_parser (PMSPA.HV L ar) (PM.PST mo dn dp (PM.SRC qc de rem) tb tg vb vk stk)).
unfold PMSPA.credit_keep. clear; lia.
- exact (L5LZ.model_rt_trans model model1 model2 MRT1 MRT2).
- exact INCLK2.
- exact INCAw2.
- exact AM2.
- change (ri_inv HI ((vb, 32 * 2 ^ vk) :: (qc, 16384) :: PM.vs_own tb ++ LBX) FF LK2 cr Aw2 M2 (vml_of model2)) in HH2.
exact (PMBRS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH2).
Qed.
Theorem end_array_ok : ltac2:(TCodec.tc2 tcn__PmBEnd "9&EvJv9vQ2v8%544321&C%146543p031").
Proof.
intros ASH. unfold PMB.end_array_spec, PMSPA.end_array_spec. cbn [pa_end_array PMB.AD ADDR_B].
apply (end_core 0xae43c 0x12e778); [lia| reflexivity| lia| lia| exact ea_run| exact ASH].
Qed.
Theorem end_object_ok : ltac2:(TCodec.tc2 tcn__PmBEnd "9&EvJv9vQ2v8%544321&D%146543p031").
Proof.
intros ASH. unfold PMB.end_object_spec, PMSPA.end_object_spec. cbn [pa_end_object PMB.AD ADDR_B].
apply (end_core 0xb02a4 0x12e7b0); [lia| reflexivity| lia| lia| exact eo_run| exact ASH].
Qed.
End WithHeap.
End PMBEND.
