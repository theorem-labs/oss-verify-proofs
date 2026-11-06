(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require BvWfKernel.
From Stdlib Require Import ZArith List Lia Bool FunctionalExtensionality.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Import Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg AsanAcct HeapIface HeapIfaceA HeapIfaceANull IcptIfaceA L5Defs L5Core L5CoreKit L5Kn L5KnA L5LazyA L5DefsA L5CoreA L5StepAR PmLayout PmLayoutA PmModel PmModelFacts PmStatics PmStaticsA HeapIfaceAJx PmSpecsA PmSpecsAX PmSpecsAa PmModelFactsA PmStep PmStepA PmAResetP PmAReset1.
Import ListNotations.
Open Scope Z_scope.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import L8Kit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5FastLia.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require Import OtfKit.
From OSSVerify.jsoncons.fuzz_ubjson_parser_max.images Require Asan.
From OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib Require TCodec.
Ltac2 tcn__PmAReset () := ([""; "Corelib.Init.Datatypes."; "Corelib.Init.Logic."; "Corelib.Numbers.BinNums."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.HeapIfaceA."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.L5Defs.L5."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmAReset.PMARS."; "OSSVerify.Proofs.jsoncons.fuzz_ubjson_parser_max.lib.PmModel.PM."; "Stdlib.Lists.List."; "Stdlib.ZArith.BinInt.Z."], [["1pair"; "1prod"; "2and"; "2eq"; "2ex"; "2not"; "3Z"; "4BIGSHADOW_HI"; "4BIGSHADOW_LO"; "5range"; "6nsh"; "6twr"; "7VLong"; "7vstr"; "8In"; "9add"]; ["9le"; "9lt"; "0a"; "0a'"; "0c"; "0n"; "0n'"; "0p"; "0r0"; "0t"; "0x"]]).
Local Ltac oF' pc := oF constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oD' pc := oD constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oE' pc := oE constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc.
Local Ltac oW' pc := oW constr:(OSSVerify.jsoncons.fuzz_ubjson_parser_max.images.Asan.M.loaded_segments) pc. Local Ltac lia := L5FastLia.plia.
Module PMARS.
Definition nsh (a n : Z) : Prop := a + n <= 2147446784 \/ 17594333495296 <= a.
Lemma nsh_sub : ltac2:(TCodec.tc2 tcn__PmAReset "H'6&:r4r3%3221&@r5%2214&?%1276r6%3215%7231z%921<%>259p021p051p0;1p0?1pQ>D1pQ8E1pQ<F1pQ6G1").
Proof. intros a n a' n'. unfold nsh. intros [X|X] H1 H2 H3; [left|right]; lia. Qed.
Lemma nsh_not : ltac2:(TCodec.tc2 tcn__PmAReset "J'6&:r3r2%3221'2&@r4%2215&A&?%1249%3291%8251&5&8%:21>&7%92@1%>231%611p081p0B1pQFG1pQ<H1pQ6I1").
Proof. intros a n x. unfold nsh, BIGSHADOW_LO, BIGSHADOW_HI. intros [X|X] H Y; lia. Qed.
Definition twr (t : PM.vstr) : list L5.range := match t with PM.VShort _ => [] | PM.VLong _ _ p => [(p, 1)] end.
Lemma in_twr : ltac2:(TCodec.tc2 tcn__PmAReset "Q0'=&9&>r1&;r2%211%53641'4'6'2'3r6(<r3%231:<%53@41r5(0+1%24;;A1%:3D41%<261qQ@>1%@2?1qQ<@1%B2A1qQ:B1%D2C1p0F1pQBM1pQDO1").
Proof. intros t r0. destruct t as [n|c n p]; cbn; [intros []| intros [<-|[]]; eauto]. Qed.
Lemma twr_in : ltac2:(TCodec.tc2 tcn__PmAReset "I'='6'3r4(<r3r2r1%43321%73961&>'1%12;;(0+1%24>>91&;r5%211%93741p0;1pQ@D1pQ<E1pQ:F1pQDH1").
Proof. intros t c n p. intros ->. left. reflexivity. Qed.
Lemma vs_own_reset t : PM.vs_own (match t with PM.VShort _ => PM.VShort 0 | PM.VLong c _ p => PM.VLong c 0 p end) = PM.vs_own t.
Proof. destruct t; reflexivity. Qed.
Lemma reset_tb_long t c n p : match t with PM.VShort _ => PM.VShort 0 | PM.VLong c _ p => PM.VLong c 0 p end = PM.VLong c n p ->
exists n', t = PM.VLong c n' p.
Proof. destruct t as [m|c' m p']; cbn; intros E; [discriminate E|]. injection E as -> _ ->. eauto. Qed.
Ltac inl := apply L5K.In_of_mem; vm_compute; reflexivity.
Abbreviation reg i := (Z_to_bv 5 (Z.of_nat i)).
Abbreviation RSEGS := Asan.M.loaded_segments.
Section WithHeap.
Context {SCFG_P : ScfgP}.
Variables (L : asan_layout) (ar : asan_run) (C : asan_statics_cells) (HI : asan_iface).
Hypothesis LY : PMA.layout L C.
Hypothesis HIok : HAJ.asan_iface_okR L ar C SCFG HI.
Let LYa := PMA.ly_as0 L C LY.
Theorem reset_ok : PMA.ann_shrink_spec L ar HI -> PMA.push_miu_spec L ar HI -> PMA.reset_spec L ar HI.
Proof.
intros ASH PSH. unfold PMA.reset_spec, PMSPA.reset_spec.
intros fx R M model K LBX FF LK Aw cr sp r fb s HH AM K0 ENT FRM FRS FOK A10 PA LEN KONT.
destruct ENT as (Rra & RAok & Rsp & Rgp & Rtp & ASTK & STKSH). change (PMSPA.pm_scr 1) with 14336 in *. change (14336 / 8) with 1792 in STKSH.
pose proof AM as (Mh & MI). pose proof ASTK as (A16 & SLO & SHI & SPT & SDEF & SUP). pose proof RAok as (Hr1 & Hr2).
rewrite L5K.rl1 in Rra. rewrite L5K.rl2 in Rsp. rewrite L5K.rl3 in Rgp. rewrite L5K.rl4 in Rtp. rewrite L5K.rl10 in A10.
destruct FOK as ((rs & Hfb) & Fal).
set (op := PMSPA.o_p PMA.AD fb) in *. assert (Eop : op = fb + 464) by reflexivity.
set (ois := PMSPA.o_is PMA.AD fb) in *.
pose proof (HAJ.aior_wf _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as (WB & WF & FSAPP & FSCEIL & FSIMG & FSSH & STSH & _ & _ & STOP & ND & _).
pose proof (WF _ Hfb) as (F1 & F2 & F3 & F4 & F5 & F6). cbn [ff_addr ff_class fst snd] in F1, F2, F3, F4, F5, F6. change (ff_bytes 4) with 1024 in *.
unfold app_mem, FS_BYTES in FSAPP, FSCEIL.
assert (AOF : forall a n, fb + 32 <= a -> a + n <= fb + 1016 -> PMSPA.aobjA FF a n).
{ intros a n H1 H2. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. lia. }
assert (O8 : op mod 8 = 0).
{ rewrite Eop. pose proof (Z.div_mod fb 1024 ltac:(lia)) as E. rewrite Fal, Z.add_0_r in E. rewrite E.
replace (1024 * (fb / 1024) + 464) with ((128 * (fb / 1024) + 58) * 8) by lia. apply Z_mod_mult. }
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK cr Aw M model HH) as (HOFF & VIS & VIMG & VFS & VBLK & VBSH & VFSSH & VSTSH).
set (H := ahid Aw model) in *. set (MV := mrestrict H M) in *.
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK cr Aw M model op 384 sp 14336 HH (PMKA.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8) ltac:(lia) ltac:(reflexivity))
as ((O1 & O2 & O3 & O4 & O5) & OBIG & ODEF & OVIS & OSHV & OCL & OSHCL).
pose proof (HAJ.aior_statics _ _ _ _ _ HIok _ _ _ _ _ _ _ HH) as ST. rewrite (L5A.aly_segs L C LYa) in ST.
pose proof (L5A.statics_facts L C M LYa ST) as (GOT & CSB & CUAR & _).
assert (HO : bv_unsigned (getr R (reg 10)) = op) by (rewrite A10; apply L5.unsigned_lit; lia).
pose proof PA as (P0 & PD & PC0 & P8 & P9 & P12 & P16 & P20 & PNI & PSRC & P320 & P328 & PC320 & PTB & PVEC & PB1 & PB2 & PB3).
set (src := PM.p_src s) in *. set (b := PM.p_b s) in *. set (k := PM.p_k s) in *. set (stk := PM.p_stk s) in *. set (tb := PM.p_tb s) in *.
set (qc := PM.sr_qc src) in *.
pose proof PVEC as (V0 & V8 & V16 & Hk & Hlen & Hal & DB & CB & AN & EL).
pose proof (PM.pow2_pos k ltac:(lia)) as P2k.
assert (P2kh : 2 ^ k <= 2 ^ 11) by (apply Z.pow_le_mono_r; lia). change (2 ^ 11) with 2048 in P2kh.
assert (Iq : In (qc, PM.CHUNK) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; left; reflexivity).
assert (Ib : In (b, 32 * 2 ^ k) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; right; left; reflexivity).
pose proof (WB _ Ib) as ((Bb0 & Bb1 & Bb2 & Bb3 & Bb4 & Bb5) & _ & _ & _ & _ & _ & _). cbn [fst snd] in Bb0, Bb1, Bb2, Bb3, Bb4, Bb5.
pose proof (WB _ Iq) as ((Bq0 & Bq1 & Bq2 & Bq3 & Bq4 & Bq5) & _ & _ & _ & _ & _ & _). cbn [fst snd] in Bq0, Bq1, Bq2, Bq3, Bq4, Bq5.
unfold app_mem, BIGSHADOW_LO, BIGSHADOW_HI in Bb5, Bq5, OBIG. unfold PM.CHUNK in *.
set (LBc := (qc, 16384) :: PM.vs_own tb ++ LBX).
assert (EPO : PM.parser_own s ++ LBX = (qc, 16384) :: (b, 32 * 2 ^ k) :: PM.vs_own tb ++ LBX) by reflexivity.
assert (INCc : incl LBc (PM.parser_own s ++ LBX)).
{ intros x Hx. rewrite EPO. destruct Hx as [<-|Hx]; [left; reflexivity| right; right; exact Hx]. }
assert (INCx : incl LBX LBc) by (intros x Hx; right; apply in_or_app; right; exact Hx).
assert (BRB : forall x, In x LBc -> 0 <= fst x /\ fst x + snd x <= 2 ^ 47).
{ intros x Hx. destruct (proj1 (WB x (INCc x Hx))) as (X0 & _ & _ & _ & _ & X5). clear - X0 X5. unfold app_mem in X5. lia. }
assert (FRB : forall f, In f FF -> 0 <= ff_addr f /\ ff_addr f + ff_bytes (ff_class f) <= 2 ^ 47).
{ intros f Hf. destruct (WF f Hf) as (X1 & X2 & _). clear - X1 X2 FSAPP. unfold FS_BYTES in *. lia. }
destruct FSAPP as (FSA0 & FSA1 & FSA2). change (nsh (ar_fs ar) 11571200) in FSA1.
assert (OPN : nsh op 384) by (unfold nsh; destruct OBIG as [X|X]; [right| left]; lia). clear OBIG.
assert (BBN : nsh b (32 * 2 ^ k)) by (destruct Bb5 as (_ & X & _); unfold nsh; destruct X; [left|right]; lia).
assert (BQN : nsh qc 16384) by (destruct Bq5 as (_ & X & _); unfold nsh; destruct X; [left|right]; lia).
assert (Bb47 : b + 32 * 2 ^ k <= 2 ^ 47) by (destruct Bb5 as (_ & _ & X); exact X).
assert (Bq47 : qc + 16384 <= 2 ^ 47) by (destruct Bq5 as (_ & _ & X); exact X).
clear Bb5 Bq5 Bb1 Bq1 FSIMG PB1 PB2 PB3.
assert (OPS : op + 384 + 4096 + 14336 <= sp) by (clear - F2 FSCEIL SLO Eop; unfold FS_BYTES in *; lia).
assert (ITB : forall c n p, tb = PM.VLong c n p -> In (p, c) (PM.parser_own s)).
{ intros c n p E. unfold PM.parser_own. change (PM.p_tb s) with tb. rewrite E. cbn [PM.src_own PM.vec_own PM.vs_own app]. right; right; left; reflexivity. }
assert (FAb : b + 32 * 2 ^ k <= fb \/ fb + 1024 <= b).
{ pose proof (WB _ Ib) as (_ & _ & _ & _ & _ & FA & _). destruct (FA (fb, 4, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X|X]; cbn [ff_addr ff_class fst snd] in X;
change (ff_bytes 4) with 1024 in X; [left|right]; lia. }
assert (FAq : qc + 16384 <= fb \/ fb + 1024 <= qc).
{ pose proof (WB _ Iq) as (_ & _ & _ & _ & _ & FA & _). destruct (FA (fb, 4, rs) (in_or_app _ _ _ (or_introl Hfb))) as [X|X]; cbn [ff_addr ff_class fst snd] in X;
change (ff_bytes 4) with 1024 in X; [left|right]; lia. }
assert (TBB : forall c n p, tb = PM.VLong c n p ->
26 <= c /\ 4096 <= p /\ p mod 16 = 0 /\ p + c <= 2 ^ 47 /\ nsh p c /\ p + c <= ahl_ceil ar
/\ (p + c <= fb \/ fb + 1024 <= p) /\ (p + c <= qc \/ qc + 16384 <= p) /\ (p + c <= b \/ b + 32 * 2 ^ k <= p)
/\ In (p, c) LBc).
{ intros c n p E. pose proof PTB as (_ & _ & X). rewrite E in X. destruct X as (_ & _ & _ & _ & Hc & _).
assert (Ip : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; exact (ITB c n p E)).
pose proof (WB _ Ip) as ((Y0 & Y1 & Y2 & Y3 & Y4 & Y5) & _ & _ & _ & AP & FA & _). cbn [fst snd] in Y0, Y1, Y2, Y3, Y4, Y5, AP.
assert (Nq : qc <> p).
{ apply (PMARS1.fst_neq_app [(qc, 16384)] ((b, 32 * 2 ^ k) :: PM.vs_own tb ++ LBX) qc 16384 p c ND); [left; reflexivity|]. rewrite E. right; left; reflexivity. }
assert (Nb : b <> p).
{ apply (PMARS1.fst_neq_app [(qc, 16384); (b, 32 * 2 ^ k)] (PM.vs_own tb ++ LBX) b (32 * 2 ^ k) p c ND); [right; left; reflexivity|]. rewrite E. left; reflexivity. }
pose proof (L5C.blocks_apart_in p c _ qc 16384 AP (L5C.in_lb_remove_neq p qc 16384 _ Iq Nq)) as Aq.
pose proof (L5C.blocks_apart_in p c _ b (32 * 2 ^ k) AP (L5C.in_lb_remove_neq p b (32 * 2 ^ k) _ Ib Nb)) as Ab.
destruct (FA (fb, 4, rs) (in_or_app _ _ _ (or_introl Hfb))) as [Z|Z]; cbn [ff_addr ff_class fst snd] in Z; change (ff_bytes 4) with 1024 in Z.
all: unfold app_mem in Y5; split; [lia|]; split; [lia|]; split; [exact Y2|]; split; [lia|]; split; [unfold nsh; destruct Y5 as (_ & [W|W] & _); unfold BIGSHADOW_LO, BIGSHADOW_HI in W; [left|right]; lia|].
all: split; [lia|]; split; [lia|]; split; [destruct Aq; lia|]; split; [destruct Ab; lia|].
all: right; apply in_or_app; left; rewrite E; left; reflexivity. }
set (TW := twr tb).
set (Wg := [(op + 8, 8); (op + 336, 24); (op + 360, 24)] ++ TW).
set (W14 := [(op + 360, 24)]). set (W15 := [(op + 8, 8); (op + 360, 24)]).
assert (WAPPg : PMKA.wapp Wg).
{ unfold Wg. apply PMKA.wapp_app.
- repeat apply PMKA.wapp_cons; [..|apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; unfold nsh in OPN; destruct OPN; [left|right|left|right|left|right]; lia.
- intros r0 Hr. destruct (in_twr tb r0 Hr) as (c & n & p & E & ->). cbn [fst snd].
destruct (TBB c n p E) as (X0 & _ & _ & _ & X & _). unfold nsh, BIGSHADOW_LO, BIGSHADOW_HI in *. destruct X; [left|right]; lia. }
assert (WAPP15 : PMKA.wapp W15).
{ unfold W15. repeat apply PMKA.wapp_cons; [..|apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; unfold nsh in OPN; destruct OPN; [left|right|left|right]; lia. }
assert (WAPP14 : PMKA.wapp W14).
{ unfold W14. repeat apply PMKA.wapp_cons; [..|apply PMKA.wapp_nil]; cbn [fst snd]; unfold BIGSHADOW_LO, BIGSHADOW_HI; unfold nsh in OPN; destruct OPN; [left|right]; lia. }
assert (OCLc : forall a, op <= a < op + 384 -> aclient L ar LBc FF sp 14336 a).
{ intros a Ha. unfold aclient, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd].
change (ff_bytes 4) with 1024. split; [lia| intros X; lia]. }
set (Wsp := [(op + 8, 8); (op + 336, 24); (op + 360, 24)]).
assert (TAIL : forall (fx1 : FPState) (R1 : bvmap 5 word) (M1 : word -> option byte) (model1 : Model) (P1 : Z -> Prop),
ri_inv HI (PM.parser_own s ++ LBX) FF LK cr Aw M1 (vml_of model1) -> L5CA.amodel_ok Aw model1 -> model_rt model model1 -> mem_grows M M1 ->
(forall a, 0 <= a < 2 ^ 64 -> ~ P1 a -> M1 (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
(forall a, P1 a -> (sp - 48 <= a < sp) \/ (op + 8 <= a < op + 10) \/ (op + 336 <= a < op + 360) \/ (op + 368 <= a < op + 376)
\/ (exists c n p, tb = PM.VLong c n p /\ p <= a < p + 1)) ->
getr R1 (reg 1) = Z_to_bv 64 0xac0ac -> getr R1 (reg 2) = Z_to_bv 64 (sp - 48) -> getr R1 (reg 8) = Z_to_bv 64 op ->
getr R1 (reg 9) = Z_to_bv 64 (op + 360) -> getr R1 (reg 10) = Z_to_bv 64 (op + 360) ->
getr R1 (reg 11) = Z_to_bv 64 (Z.of_nat (length stk)) -> getr R1 (reg 18) = Z_to_bv 64 2147450880 ->
(forall j, In j [3; 4; 19; 20; 21; 22; 23; 24; 25; 26; 27]%nat -> getr R1 (reg j) = getr R (reg j)) ->
L5.u64_at RSEGS M1 (sp - 8) (bv_unsigned (getr R (reg 1))) -> L5.u64_at RSEGS M1 (sp - 16) (bv_unsigned (getr R (reg 8))) ->
L5.u64_at RSEGS M1 (sp - 24) (bv_unsigned (getr R (reg 9))) -> L5.u64_at RSEGS M1 (sp - 32) (bv_unsigned (getr R (reg 18))) ->
L5.u8_at RSEGS M1 (op + 8) 1 -> L5.u8_at RSEGS M1 (op + 9) 0 -> L5.u64_at RSEGS M1 (op + 368) b ->
PM.vstr_at RSEGS PMSPA.accA M1 (op + 336) (PM.p_tb (PMSPA.pst_reset s)) ->
srealizes RSEGS SCFG (@PMSPA.cfg RSEGS fx1 R1 0xaa778 M1 model1) K).
{ intros fx1 R1 M1 model1 P1 HH1 AM1 MRT1 MG1 FR1 HP1 R1ra R1sp R1s0 R1s1 R1a0 R1a1 R1s2 R1cs SV8 SV16 SV24 SV32 C8 C9 C368 TB1.
assert (P1sh : forall x, BIGSHADOW_LO <= x < BIGSHADOW_HI -> ~ P1 x).
{ intros x Hx X. destruct (HP1 x X) as [Y|[Y|[Y|[Y|(c0 & n0 & p0 & Etb & Y)]]]].
- clear - Hx Y SLO SPT. unfold BIGSHADOW_LO, BIGSHADOW_HI in *. lia.
- exact (nsh_not op 384 x OPN ltac:(lia) Hx).
- exact (nsh_not op 384 x OPN ltac:(lia) Hx).
- exact (nsh_not op 384 x OPN ltac:(lia) Hx).
- destruct (TBB c0 n0 p0 Etb) as (X0 & _ & _ & _ & X4 & _). exact (nsh_not p0 c0 x X4 ltac:(lia) Hx). }
assert (NP1 : forall i, ~ (sp - 48 <= i < sp) -> ~ (op + 8 <= i < op + 10) -> ~ (op + 336 <= i < op + 360) -> ~ (op + 368 <= i < op + 376) ->
(forall c n p, tb = PM.VLong c n p -> ~ (p <= i < p + 1)) -> ~ P1 i).
{ intros i N1 N2 N3 N4 N5 X. destruct (HP1 i X) as [Y|[Y|[Y|[Y|(c0 & n0 & p0 & Etb & Y)]]]]; [exact (N1 Y)|exact (N2 Y)|exact (N3 Y)|exact (N4 Y)| exact (N5 c0 n0 p0 Etb Y)]. }
assert (SHM1 : forall a n, 0 <= a -> a + n <= 2 ^ 47 -> PMFA.agsh M M1 a n).
{ intros a n Ha Hn x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX. apply FR1; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| apply P1sh; exact SX]. }
assert (SZk : forall lo g, lo mod 8 = 0 -> 0 <= lo -> lo + 8 * g <= 2 ^ 47 -> 0 <= g -> shadow_zero M lo g -> shadow_zero M1 lo g).
{ intros lo g Hlo H0 H1 Hg SZ j Hj. pose proof (SZ j Hj) as Z1. unfold byte_at in *. rewrite (PMFA.S_granule lo j Hlo ltac:(lia)) in *.
pose proof (PMKA.S_in_shadow (lo + 8 * j) ltac:(lia)) as SX. rewrite FR1; [exact Z1| unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| apply P1sh; exact SX]. }
assert (NPop : forall i, op <= i < op + 384 -> ~ (op + 8 <= i < op + 10) -> ~ (op + 336 <= i < op + 360) -> ~ (op + 368 <= i < op + 376) -> ~ P1 i).
{ intros i Hi N2 N3 N4. apply NP1; [lia| exact N2| exact N3| exact N4|]. intros c n p E Y. destruct (TBB c n p E) as (X0 & _ & _ & _ & _ & _ & X & _). lia. }
assert (NPb : forall i, b <= i < b + 32 * 2 ^ k -> ~ P1 i).
{ intros i Hi. apply NP1; [clear - Hi Bb4 SLO; lia| clear - Hi FAb Eop; lia| clear - Hi FAb Eop; lia| clear - Hi FAb Eop; lia|]. intros c n p E Y. destruct (TBB c n p E) as (X0 & _ & _ & _ & _ & _ & _ & _ & X & _). lia. }
rewrite EPO in HH1. pose proof (PMARS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH1) as HH1s.
change (ri_inv HI (PM.vec_own b k ++ LBc) FF LK cr Aw M1 (vml_of model1)) in HH1s. rewrite <- EPO in HH1.
assert (ASTK1 : L5CA.astk ar M1 sp 14336) by exact (L5SAR.astk_grows ar M M1 sp 14336 ASTK MG1).
assert (ASTK1c : L5CA.astk ar M1 (sp - 48) 12288).
{ apply (L5SAR.astk_sub ar M M1 sp 14336 48 12288 ASTK MG1); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
assert (SZ0 : shadow_zero M (sp - 12336) 1536).
{ apply (PMKA.shadow_zero_sub M (sp - 14336) 1792); [| | lia| lia| lia| exact STKSH].
+ apply PMKA.mod16_8'. replace (sp - 14336) with (sp + (-896) * 16) by lia. rewrite Z_mod_plus_full. exact A16.
+ apply PMKA.mod16_8'. replace (sp - 12336) with (sp + (-771) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
assert (SZ1 : shadow_zero M1 (sp - 12336) 1536).
{ apply SZk; [| lia| lia| lia| exact SZ0]. apply PMKA.mod16_8'. replace (sp - 12336) with (sp + (-771) * 16) by lia. rewrite Z_mod_plus_full. exact A16. }
assert (AGv1 : L5C.agree_on M M1 (op + 360) 8) by (intros i Hi; apply FR1; [lia| apply NPop; lia]).
assert (AGv16 : L5C.agree_on M M1 (op + 376) 8) by (intros i Hi; apply FR1; [lia| apply NPop; lia]).
unfold PMA.ann_shrink_spec, PMSAX.ann_shrink_spec in ASH. cbn [paa_ann_shrink PMA.AAD AADDR_A] in ASH.
apply (ASH fx1 R1 M1 model1 K LBc FF LK Aw cr (op + 360) b k (Z.of_nat (length stk)) [] (sp - 48) 0xac0ac HH1s AM1 K0).
{ split; [rewrite L5K.rl1; exact R1ra|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; exact R1sp|].
split; [rewrite L5K.rl3; rewrite (R1cs 3%nat) by inl; exact Rgp|]. split; [rewrite L5K.rl4; rewrite (R1cs 4%nat) by inl; exact Rtp|].
change (PMSPA.pm_scr 0) with 12288. split; [exact ASTK1c|]. change (12288 / 8) with 1536. replace (sp - 48 - 12288) with (sp - 12336) by lia. exact SZ1. }
{ intros f Hf. specialize (FRS f Hf). lia. }
{ rewrite L5K.rl10. exact R1a0. }
{ rewrite L5K.rl11. exact R1a1. }
{ apply AOF; lia. }
{ replace (op + 360) with (op + 45 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
{ apply (PMFA.accA_agree M M1); [apply SHM1; lia|]. intros a Ha. apply PC320. lia. }
{ cbn [length]. lia. }
{ apply (L5C.u64_at_agree RSEGS M M1); [exact AGv1|lia|lia|exact V0]. }
{ cbn [length]. replace (op + 360 + 8) with (op + 368) by lia. replace (b + 32 * Z.of_nat 0) with b by lia. exact C368. }
{ replace (op + 360 + 16) with (op + 376) in * by lia. apply (L5C.u64_at_agree RSEGS M M1); [exact AGv16|lia|lia|exact V16]. }
{ lia. }
{ exact Hal. }
{ intros i Hi. apply MG1. apply DB. exact Hi. }
{ apply (PMFA.accA_agree M M1); [apply SHM1; lia| exact CB]. }
{ apply (PMFA.annA_agree M M1); [apply PMKA.mod16_8'; exact Hal| lia| |apply SHM1; lia| exact AN].
replace (32 * 2 ^ k) with ((4 * 2 ^ k) * 8) by lia. apply Z_mod_mult. }
{ intros i Hi. cbn [length] in Hi. lia. }
intros fx2 R2 M2 model2 LK2 Aw2 RP2 VEC2 ACC2 HP2 MRT2 INCLK2 INCAw2 AM2 HH2.
change (PMSPA.pm_scr 0) with 12288 in HP2.
assert (ASTK2 : L5CA.astk ar M2 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBc FF M1 M2 sp 14336 (sp - 48) 12288 [] ASTK1 HP2); lia).
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 HH2) as (_ & VIS2 & _).
set (H2 := ahid Aw2 model2) in *. set (MV2 := mrestrict H2 M2) in *.
assert (G2 : getr R2 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R1 R2 2 RP2) by inl; exact R1sp).
assert (G8 : getr R2 (reg 8) = Z_to_bv 64 op) by (rewrite (L5SAR.cs_of_preserved R1 R2 8 RP2) by inl; exact R1s0).
assert (G9 : getr R2 (reg 9) = Z_to_bv 64 (op + 360)) by (rewrite (L5SAR.cs_of_preserved R1 R2 9 RP2) by inl; exact R1s1).
assert (G18 : getr R2 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R1 R2 18 RP2) by inl; exact R1s2).
assert (W2 : L5.writable RSEGS MV2 (sp - 48) 48).
{ pose proof ASTK2 as (_ & _ & _ & _ & SDEF2 & _).
apply (proj2 (L5A.writable_vis H2 M2 (sp - 48) 48 (VIS2 (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M2 (sp - 14336) 14336); [exact SDEF2| lia| lia]. lia. lia. }
cfeed P (PMARSP.arsM_conc fx2 R2 MV2 (fun j => match j with 2%nat => sp | 40%nat => op | _ => 0 end)) ltac:(first [assumption | unfold PMARSP.aligned; lia | lia]).
destruct P as (fx3 & R3 & M3v & MG3 & _ & FRZ3 & MS3 & KS3 & A31 & A310 & A311 & A312 & A313 & C341 & C340 & C336).
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 model2 fx2 fx3 R2 0xac0ac R3 0xacda8 M3v (fun a => sp - 41 <= a < sp - 41 + 9) K HH2 AM2 MS3 MG3 FRZ3).
{ intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. right; left. split; [lia| intros X; lia]. }
intros M3 model3 HH3 AM3 MRT3 HID3 VIS3 MGM3 FR3 VV3.
assert (EK01 : L5SAR.ek L ar LBc FF sp 14336 Wg M M1).
{ apply (L5SAR.ek_piece L ar LBc FF sp 14336 Wg M M1 P1 FR1). intros a Ha Hc Ho X.
destruct (HP1 a X) as [Y|[Y|[Y|[Y|(c0 & n0 & p0 & Etb & Y)]]]].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M1 _ sp 14336 a HH1s SPT (L5SAR.aclient_appb L ar LBc (PM.vec_own b k) FF sp 14336 a Hc))
as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
- apply (Ho (op + 8, 8)); [unfold Wg; cbn [app In]; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (Ho (op + 336, 24)); [unfold Wg; cbn [app In]; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (Ho (op + 360, 24)); [unfold Wg; cbn [app In]; right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (Ho (p0, 1)); [| unfold L5.in_rng; cbn [fst snd]; lia]. unfold Wg. apply in_or_app. right. exact (twr_in tb c0 n0 p0 Etb). }
assert (EK12 : L5SAR.ek L ar LBc FF sp 14336 W14 M1 M2).
{ apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 (sp - 48) 12288 W14 [] M1 M2 HP2); [lia| lia| intros a _ _ r0 []]. }
assert (EK23 : L5SAR.ek L ar LBc FF sp 14336 W14 M2 M3).
{ apply (L5SAR.ek_piece L ar LBc FF sp 14336 W14 M2 M3 (fun a => sp - 41 <= a < sp - 41 + 9) FR3). intros a Ha Hc _ X.
destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK2 cr Aw2 M2 _ sp 14336 a HH2 SPT (L5SAR.aclient_appb L ar LBc (PM.vec_own b k) FF sp 14336 a Hc))
as [(_ & Z2)|Z2]; [apply Z2; lia| lia]. }
assert (EKW : forall M' M'', L5SAR.ek L ar LBc FF sp 14336 W14 M' M'' -> L5SAR.ek L ar LBc FF sp 14336 Wg M' M'').
{ intros M' M'' E. apply (L5SAR.ek_W L ar LBc FF sp 14336 Wg W14 M' M'' E). intros a O r0 [<-|[]] X.
apply (O (op + 360, 24)); [unfold Wg; cbn [app In]; right; right; left; reflexivity| exact X]. }
pose proof (L5SAR.ek_trans L ar LBc FF sp 14336 Wg M M1 M3 EK01 (EKW _ _ (L5SAR.ek_trans L ar LBc FF sp 14336 W14 M1 M2 M3 EK12 EK23))) as EK03.
assert (SP16 : forall j, (sp - 16 * j) mod 8 = 0) by (intros j; apply PMKA.mod16_8'; replace (sp - 16 * j) with (sp + (- j) * 16) by lia; rewrite Z_mod_plus_full; exact A16).
assert (SZ3 : shadow_zero M3 (sp - 14336) 1792).
{ apply (PMKA.stksh_keepA L ar LBc FF sp 14336 Wg M M3 EK03 WAPPg (sp - 14336) 1792); [lia|lia|lia| | lia| exact STKSH].
replace (sp - 14336) with (sp - 16 * 896) by lia. apply SP16. }
assert (SZ3c : shadow_zero M3 (sp - 12336) 1536).
{ apply (PMKA.shadow_zero_sub M3 (sp - 14336) 1792); [| |lia|lia|lia| exact SZ3].
+ replace (sp - 14336) with (sp - 16 * 896) by lia. apply SP16. + replace (sp - 12336) with (sp - 16 * 771) by lia. apply SP16. }
assert (AC3 : forall a n, sp - 14336 <= a -> a + n <= sp -> PMSPA.accA M3 a n).
{ intros a n H1' H2'. apply (PMARS1.acc_of_shadow_zero M3 (sp - 14336) 1792 a n SZ3); [| lia| lia].
replace (sp - 14336) with (sp - 16 * 896) by lia. apply SP16. }
assert (ASTK3 : L5CA.astk ar M3 sp 14336) by exact (L5SAR.astk_grows ar M2 M3 sp 14336 ASTK2 MGM3).
assert (BZ3 : forall p, sp - 14336 <= p < sp -> byte_at M3 (HeapIfaceA.S p) 0).
{ intros p Hp. pose proof (SP16 896) as S16. replace (sp - 16 * 896) with (sp - 14336) in S16 by lia.
assert (E : HeapIfaceA.S p = HeapIfaceA.S (sp - 14336) + (p / 8 - (sp - 14336) / 8)) by (unfold HeapIfaceA.S; lia).
rewrite E. apply SZ3. Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). clear - Hp S16. lia. }
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
assert (SP4 : sp mod 4 = 0).
{ apply Z.mod_divide; [lia|]. destruct (proj1 (Z.mod_divide sp 16 ltac:(lia)) A16) as (q & Eq). exists (4 * q). lia. }
rewrite <- VIS3 in C336, C340, C341.
apply (proj1 (L5A.u32_at_vis H2 M3 (sp - 36) 0 (VIS2 (sp - 36) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in C336.
apply (proj1 (L5A.u32_at_vis H2 M3 (sp - 40) 0 (VIS2 (sp - 40) 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in C340.
apply (proj1 (L5A.u8_at_vis H2 M3 (sp - 41) 0 (VIS2 (sp - 41) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))) in C341.
unfold PMA.push_miu_spec, PMSAX.push_miu_spec, PMSAX.push_spec_at in PSH. cbn [paa_esp_miu PMA.AAD AADDR_A] in PSH.
apply (PSH fx3 R3 M3 model3 K LBc FF LK2 Aw2 cr (op + 360) b k [] (PM.vec_own b k) PM.ps_root (sp - 48) 0xac0cc HH3 AM3 K0).
{ split; [rewrite L5K.rl1; exact A31|]. split; [split; [lia| reflexivity]|]. split; [rewrite L5K.rl2; rewrite (KS3 2%nat) by inl; exact G2|].
split; [rewrite L5K.rl3; rewrite (KS3 3%nat) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 3 RP2) by inl; rewrite (R1cs 3%nat) by inl; exact Rgp|].
split; [rewrite L5K.rl4; rewrite (KS3 4%nat) by inl; rewrite (L5SAR.cs_of_preserved R1 R2 4 RP2) by inl; rewrite (R1cs 4%nat) by inl; exact Rtp|].
change (PMSPA.pm_scr 0) with 12288. split.
{ apply (L5SAR.astk_sub ar M3 M3 sp 14336 48 12288 ASTK3 (fun _ X => X)); [lia|lia|lia|]. replace (sp - 48) with (sp + (-3) * 16) by lia. rewrite Z.mod_add by lia. exact A16. }
change (12288 / 8) with 1536. replace (sp - 48 - 12288) with (sp - 12336) by lia. exact SZ3c. }
{ intros f Hf. specialize (FRS f Hf). lia. }
{ rewrite L5K.rl10. exact A310. }
{ apply AOF; lia. }
{ replace (op + 360) with (op + 45 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
{ exact (PMKA.acc_keepA' L ar LBc FF sp 14336 W14 M2 M3 EK23 WAPP14 FRB (op + 360) 24 (AOF (op + 360) 24 ltac:(lia) ltac:(lia)) ACC2). }
{ right. split; [|reflexivity]. apply (PMFA.vec_at_agreeA RSEGS M2 M3 (op + 360) b k []); [lia|lia|lia|lia| | |exact VEC2].
- intros i Hi. apply FR3; [lia| intros X; lia].
- split; [intros i Hi; apply FR3; [lia| intros X; lia]|]. intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
unfold BIGSHADOW_LO, BIGSHADOW_HI in SX. apply FR3; [lia| intros X; lia]. }
{ intros X. discriminate X. }
{ intros [X|X]; [discriminate X| cbn [length Z.of_nat] in X; lia]. }
{ unfold PMSAX.cells_miu. exists (sp - 36), (sp - 40), (sp - 41), 0, 0, 0.
split; [rewrite L5K.rl11; exact A311|]. split; [rewrite L5K.rl12; exact A312|]. split; [rewrite L5K.rl13; exact A313|].
split; [replace (sp - 36) with (sp + (-9) * 4) by lia; rewrite Z_mod_plus_full; exact SP4|].
split; [replace (sp - 40) with (sp + (-10) * 4) by lia; rewrite Z_mod_plus_full; exact SP4|].
split; [apply AC3; lia|]. split; [apply AC3; lia|]. split; [apply AC3; lia|].
split; [split; [right; clear - SHI SPT; lia| right; clear - OPS; lia]|].
split; [split; [right; clear - SHI SPT; lia| right; clear - OPS; lia]|].
split; [split; [right; clear - SHI SPT; lia| right; clear - OPS; lia]|].
split; [apply BZ3; lia|]. split; [apply BZ3; lia|]. split; [apply BZ3; lia|].
split; [exact C336|]. split; [exact C340|]. split; [exact C341|]. split; [lia|]. split; [lia|]. split; [lia| reflexivity]. }
{ intros [X|X]; [discriminate X| cbn [length Z.of_nat] in X; lia]. }
intros fx4 R4 M4 model4 LK4 Aw4 b' k' cr' RP4 VEC4 ACC4 PO4 HP4 MRT4 INCLK4 INCAw4 AM4 HH4.
destruct PO4 as [(_ & _ & _ & Eb' & Ek' & Ecr')|(X & _ & _)];
[subst b' k' cr'| exfalso; destruct X as [X|X]; [discriminate X| cbn [length Z.of_nat] in X; lia]].
change (PMSPA.pm_scr 0) with 12288 in HP4. cbn [app] in VEC4.
assert (ASTK4 : L5CA.astk ar M4 sp 14336) by (apply (PMKA.astk_after_ahpres L ar LBc FF M3 M4 sp 14336 (sp - 48) 12288 [(op + 360, 24)] ASTK3 HP4); lia).
assert (EK34 : L5SAR.ek L ar LBc FF sp 14336 W14 M3 M4).
{ apply (L5SAR.ek_callee L ar LBc [] FF [] sp 14336 (sp - 48) 12288 W14 [(op + 360, 24)] M3 M4 HP4); [lia| lia| intros a _ O; exact O]. }
pose proof (L5SAR.ek_trans L ar LBc FF sp 14336 W14 M1 M3 M4 (L5SAR.ek_trans L ar LBc FF sp 14336 W14 M1 M2 M3 EK12 EK23) EK34) as EK14.
pose proof (L5SAR.ek_trans L ar LBc FF sp 14336 Wg M M1 M4 EK01 (EKW _ _ EK14)) as EK04.
pose proof (L5SAR.vis_pack L ar C HI LYa HIok _ FF LK4 cr Aw4 M4 model4 HH4) as (_ & VIS4 & _).
pose proof (L5SAR.aobj_facts L ar C HI LYa HIok _ FF LK4 cr Aw4 M4 model4 op 384 sp 14336 HH4 (PMKA.aobj_of_aobjA FF op 384 (AOF op 384 ltac:(lia) ltac:(lia)) O8)
ltac:(lia) ltac:(reflexivity)) as (_ & _ & _ & OVIS4 & OSHV4 & _ & _).
set (H4 := ahid Aw4 model4) in *. set (MV4 := mrestrict H4 M4) in *.
assert (Q2 : getr R4 (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (L5SAR.cs_of_preserved R3 R4 2 RP4) by inl; rewrite (KS3 2%nat) by inl; exact G2).
assert (Q8 : getr R4 (reg 8) = Z_to_bv 64 op) by (rewrite (L5SAR.cs_of_preserved R3 R4 8 RP4) by inl; rewrite (KS3 8%nat) by inl; exact G8).
assert (Q9 : getr R4 (reg 9) = Z_to_bv 64 (op + 360)) by (rewrite (L5SAR.cs_of_preserved R3 R4 9 RP4) by inl; rewrite (KS3 9%nat) by inl; exact G9).
assert (Q18 : getr R4 (reg 18) = Z_to_bv 64 2147450880) by (rewrite (L5SAR.cs_of_preserved R3 R4 18 RP4) by inl; rewrite (KS3 18%nat) by inl; exact G18).
assert (FRAME14 : forall a, sp - 32 <= a < sp -> M4 (Z_to_bv 64 a) = M1 (Z_to_bv 64 a)).
{ intros a Ha. destruct HP4 as (P4 & _). destruct HP2 as (P2 & _).
assert (CLa : forall LBz FFz, aclient L ar LBz FFz (sp - 48) 12288 a) by (intros LBz FFz; unfold aclient, aclient_g; right; left; split; [lia| intros X; lia]).
rewrite P4; [| split; [lia|]; split; [apply CLa| intros r0 [<-|[]]; unfold L5.in_rng; cbn [fst snd]; lia]].
rewrite FR3; [| lia| intros X; lia].
apply P2. split; [lia|]. split; [apply CLa| intros r0 []]. }
assert (SVV : forall j v, 1 <= j <= 4 -> L5.u64_at RSEGS M1 (sp - 8 * j) v -> L5.u64_at RSEGS MV4 (sp - 8 * j) v).
{ intros j v Hj SV. apply (proj2 (L5A.u64_at_vis H4 M4 (sp - 8 * j) v (VIS4 (sp - 8 * j) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.u64_at_agree RSEGS M1 M4); [intros i Hi; apply FRAME14; lia| lia| lia| exact SV]. }
assert (Y8 : L5.u64_at RSEGS MV4 (sp - 8) (bv_unsigned (getr R (reg 1)))) by (replace (sp - 8) with (sp - 8 * 1) by lia; apply SVV; [lia| exact SV8]).
assert (Y16 : L5.u64_at RSEGS MV4 (sp - 16) (bv_unsigned (getr R (reg 8)))) by (replace (sp - 16) with (sp - 8 * 2) by lia; apply SVV; [lia| exact SV16]).
assert (Y24 : L5.u64_at RSEGS MV4 (sp - 24) (bv_unsigned (getr R (reg 9)))) by (replace (sp - 24) with (sp - 8 * 3) by lia; apply SVV; [lia| exact SV24]).
assert (Y32 : L5.u64_at RSEGS MV4 (sp - 32) (bv_unsigned (getr R (reg 18)))) by (replace (sp - 32) with (sp - 8 * 4) by lia; apply SVV; [lia| exact SV32]).
assert (ACC4op : PMSPA.accA M4 op 24) by exact (PMKA.acc_keepA' L ar LBc FF sp 14336 Wg M M4 EK04 WAPPg FRB op 24 (AOF op 24 ltac:(lia) ltac:(lia)) PC0).
assert (Z4 : L5KA.zeros_at MV4 (((op + 12) / 8) + 2147450880) 1).
{ assert (E12 : (op + 12) / 8 = op / 8 + 1).
{ replace (op + 12) with (4 + (op / 8 + 1) * 8) by (pose proof (Z.div_mod op 8 ltac:(lia)); lia). rewrite Z.div_add by lia. lia. }
rewrite E12. apply (proj2 (L5A.zeros_at_vis H4 M4 (op / 8 + 1 + 2147450880) 1 (L5A.avis_sub H4 (op / 8 + SB) (384 / 8) (op / 8 + 1 + 2147450880) 1 OSHV4 ltac:(unfold SB; lia) ltac:(unfold SB; lia)))).
pose proof (PMKA.zeros_of_aacc M4 op 24 ACC4op O8 ltac:(reflexivity) ltac:(lia)) as ZZ. change (24 / 8) with 3 in ZZ.
intros i Hi. replace (op / 8 + 1 + 2147450880 + i) with (op / 8 + SB + (1 + i)) by (unfold SB; lia). apply ZZ. lia. }
assert (DK04 : L5SAR.dk L ar LBc FF sp 14336 M M4).
{ apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M3 M4).
- apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M2 M3).
+ apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M1 M2); [apply L5SAR.dk_grows; exact MG1|].
apply (L5SAR.dk_callee L ar LBc [] FF [] sp 14336 (sp - 48) 12288 [] M1 M2 HP2); lia.
+ apply L5SAR.dk_grows. exact MGM3.
- apply (L5SAR.dk_callee L ar LBc [] FF [] sp 14336 (sp - 48) 12288 [(op + 360, 24)] M3 M4 HP4); lia. }
assert (ODEF4 : L5.defined M4 op 384) by (intros i Hi; apply DK04; [lia| apply OCLc; lia| apply ODEF; exact Hi]).
assert (W4o : L5.writable RSEGS MV4 (op + 12) 4).
{ apply (proj2 (L5A.writable_vis H4 M4 (op + 12) 4 ltac:(eapply L5A.avis_sub; [exact OVIS4|lia|lia]) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M4 op 384); [exact ODEF4| lia| lia]. lia. lia. }
assert (W4s : L5.writable RSEGS MV4 (sp - 48) 48).
{ pose proof ASTK4 as (_ & _ & _ & _ & SDEF4 & _).
apply (proj2 (L5A.writable_vis H4 M4 (sp - 48) 48 (VIS4 (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS). apply (L5.defined_sub M4 (sp - 14336) 14336); [exact SDEF4| lia| lia]. lia. lia. }
pose proof (bv_unsigned_in_range 64 (getr R (reg 1))) as Hs1. pose proof (bv_unsigned_in_range 64 (getr R (reg 8))) as Hs8.
pose proof (bv_unsigned_in_range 64 (getr R (reg 9))) as Hs9. pose proof (bv_unsigned_in_range 64 (getr R (reg 18))) as Hs18.
change (bv_modulus 64) with (2 ^ 64) in Hs1, Hs8, Hs9, Hs18.
cfeed P (PMARSP.arsZ_conc fx4 R4 MV4 (fun j => match j with 2%nat => sp | 38%nat => bv_unsigned (getr R (reg 1)) | 39%nat => bv_unsigned (getr R (reg 8))
| 40%nat => op | 41%nat => bv_unsigned (getr R (reg 9)) | 42%nat => bv_unsigned (getr R (reg 18)) | _ => 0 end)) ltac:(first [assumption | unfold PMARSP.aligned; lia | lia]).
destruct P as (fx5 & R5 & M5v & MG5 & _ & FRZ5 & MS5 & KS5 & A51 & A52 & A58 & A59 & A510 & A511 & A518 & C512).
assert (R5ra : getr R5 (reg 1) = Z_to_bv 64 r) by (rewrite A51, Z_to_bv_bv_unsigned; exact Rra).
pose proof (PMK.ret_to RSEGS fx5 R5 M5v 0xac0f8 (ltac:(oW' 0xac0f8%Z)) r (ltac:(oF' 0xac0f8%Z)) eq_refl (ltac:(oD' 0xac0f8%Z)) R5ra Hr1 Hr2) as MS6.
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK4 cr Aw4 M4 model4 fx4 fx5 R4 0xac0cc R5 r M5v (fun a => op + 12 <= a < op + 12 + 4) K HH4 AM4).
{ eapply msteps_trans; [exact MS5| exact MS6]. }
{ exact MG5. }
{ exact FRZ5. }
{ intros a Ha Wa. split; [|intros X; lia]. unfold aclientw, aclient_g. do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|].
cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros X; lia]. }
intros M5 model5 HH5 AM5 MRT5 HID5 VIS5 MGM5 FR5 VV5.
assert (EK45 : L5SAR.ek L ar LBc FF sp 14336 W15 M4 M5).
{ apply (L5SAR.ek_piece L ar LBc FF sp 14336 W15 M4 M5 (fun a => op + 12 <= a < op + 12 + 4) FR5). intros a Ha _ Ho X.
apply (Ho (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia]. }
assert (EK15 : L5SAR.ek L ar LBc FF sp 14336 W15 M1 M5).
{ apply (L5SAR.ek_trans L ar LBc FF sp 14336 W15 M1 M4 M5); [|exact EK45].
apply (L5SAR.ek_W L ar LBc FF sp 14336 W15 W14 M1 M4 EK14). intros a O r0 [<-|[]] X. apply (O (op + 360, 24)); [right; left; reflexivity| exact X]. }
assert (EK05 : L5SAR.ek L ar LBc FF sp 14336 Wg M M5).
{ apply (L5SAR.ek_trans L ar LBc FF sp 14336 Wg M M1 M5 EK01). apply (L5SAR.ek_W L ar LBc FF sp 14336 Wg W15 M1 M5 EK15).
intros a O r0 Hr X. destruct Hr as [<-|[<-|[]]].
- apply (O (op + 8, 8)); [unfold Wg; cbn [app In]; left; reflexivity| exact X].
- apply (O (op + 360, 24)); [unfold Wg; cbn [app In]; right; right; left; reflexivity| exact X]. }
assert (EK01x : L5SAR.ek L ar LBX FF sp 14336 Wsp M M1).
{ apply (L5SAR.ek_piece L ar LBX FF sp 14336 Wsp M M1 P1 FR1). intros a Ha Hc Ho X.
destruct (HP1 a X) as [Y|[Y|[Y|[Y|(c0 & n0 & p0 & Etb & Y)]]]].
- destruct (L5SAR.aclient_cases L ar C HI LYa HIok _ FF LK cr Aw M _ sp 14336 a HH SPT (L5SAR.aclient_appb L ar LBX (PM.parser_own s) FF sp 14336 a Hc))
as [(_ & Z2)|Z2]; [apply Z2; lia| lia].
- apply (Ho (op + 8, 8)); [left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (Ho (op + 336, 24)); [right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- apply (Ho (op + 360, 24)); [right; right; left; reflexivity| unfold L5.in_rng; cbn [fst snd]; lia].
- destruct (TBB c0 n0 p0 Etb) as (X0 & _).
exact (PMARS1.own_not_aclient L ar C HI HIok (PM.parser_own s) LBX FF LK cr Aw M _ p0 c0 a sp 14336 HH (ITB c0 n0 p0 Etb) ltac:(lia) Hc). }
assert (EK05x : L5SAR.ek L ar LBX FF sp 14336 Wsp M M5).
{ apply (L5SAR.ek_trans L ar LBX FF sp 14336 Wsp M M1 M5 EK01x).
apply (L5SAR.ek_W L ar LBX FF sp 14336 Wsp W15 M1 M5 (PMKA.ek_sublb L ar LBc LBX FF sp 14336 W15 M1 M5 INCx EK15)).
intros a O r0 Hr X. destruct Hr as [<-|[<-|[]]]; [apply (O (op + 8, 8))| apply (O (op + 360, 24))]; [left; reflexivity| exact X| right; right; left; reflexivity| exact X]. }
assert (DK05 : L5SAR.dk L ar LBc FF sp 14336 M M5) by (apply (L5SAR.dk_trans L ar LBc FF sp 14336 M M4 M5 DK04); apply L5SAR.dk_grows; exact MGM5).
assert (ASTK5 : L5CA.astk ar M5 sp 14336) by exact (L5SAR.astk_grows ar M4 M5 sp 14336 ASTK4 MGM5).
assert (OUTg : forall i, ~ (op + 8 <= i < op + 16) -> ~ (op + 336 <= i < op + 384) -> (forall c n p, tb = PM.VLong c n p -> ~ (p <= i < p + 1)) -> L5.outside Wg i).
{ intros i N1 N2 N3 r0 Hr. unfold Wg in Hr. apply in_app_or in Hr. destruct Hr as [Hr|Hr].
- destruct Hr as [<-|[<-|[<-|[]]]]; unfold L5.in_rng; cbn [fst snd]; lia.
- destruct (in_twr tb r0 Hr) as (c0 & n0 & p0 & E0 & ->). unfold L5.in_rng; cbn [fst snd]. exact (N3 c0 n0 p0 E0). }
assert (AG5 : forall a, 0 <= a < 2 ^ 64 -> ~ (op + 12 <= a < op + 16) -> M5 (Z_to_bv 64 a) = M4 (Z_to_bv 64 a)).
{ intros a Ha N. apply FR5; [exact Ha| intros X; apply N; lia]. }
apply (KONT fx5 R5 M5 model5 LK4 Aw4).
-
apply L5SAR.preserved_by_index. intros j Hj. unfold L5SAR.cs_all in Hj.
repeat (destruct Hj as [<-|Hj];
[ first [ rewrite A52; exact (eq_sym Rsp)
| rewrite A58; apply Z_to_bv_bv_unsigned | rewrite A59; apply Z_to_bv_bv_unsigned | rewrite A518; apply Z_to_bv_bv_unsigned
| rewrite (KS5 _) by inl; rewrite (L5SAR.cs_of_preserved R3 R4 _ RP4) by inl; rewrite (KS3 _) by inl;
rewrite (L5SAR.cs_of_preserved R1 R2 _ RP2) by inl; apply R1cs; inl ] |]).
destruct Hj.
-
apply (PMARS1.reset_postA M M5 op ois s PA LEN); [lia| lia| change (PM.sr_qc (PM.p_src s)) with qc; lia| change (PM.sr_qc (PM.p_src s)) with qc; unfold PM.CHUNK; lia| | | | | | | | | | ].
+ apply (PMKA.agA_obj L ar LBc FF sp 14336 Wg M M5 EK05 WAPPg FRB op 8 (AOF op 8 ltac:(lia) ltac:(lia))).
intros i Hi. apply OUTg; [lia| lia|]. intros c n p E Y. destruct (TBB c n p E) as (X0 & _ & _ & _ & _ & _ & X & _). lia.
+ apply (PMKA.agA_obj L ar LBc FF sp 14336 Wg M M5 EK05 WAPPg FRB (op + 16) 320 (AOF (op + 16) 320 ltac:(lia) ltac:(lia))).
intros i Hi. apply OUTg; [lia| lia|]. intros c n p E Y. destruct (TBB c n p E) as (X0 & _ & _ & _ & _ & _ & X & _). lia.
+ exact (PMKA.agsh_obj L ar LBc FF sp 14336 Wg M M5 EK05 WAPPg FRB op 384 (AOF op 384 ltac:(lia) ltac:(lia))).
+ apply (PMKA.agA_blk L ar LBc FF sp 14336 Wg M M5 EK05 WAPPg BRB qc 16384 (or_introl eq_refl)).
intros i Hi. apply OUTg; [lia| lia|]. intros c n p E Y. destruct (TBB c n p E) as (X0 & _ & _ & _ & _ & _ & _ & X & _). lia.
+ intros i Hi. apply DK05; [lia| apply OCLc; lia| apply ODEF; exact Hi].
+ apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply AG5; lia| lia| lia|].
apply (PMKA.u8_keepA RSEGS L ar LBc FF sp 14336 W14 M1 M4 EK14 WAPP14 FRB (op + 8) 1 (AOF (op + 8) 1 ltac:(lia) ltac:(lia))); [| exact C8].
intros i Hi r0 [<-|[]]. unfold L5.in_rng; cbn [fst snd]; lia.
+ apply (L5C.u8_at_agree RSEGS M4 M5); [intros i Hi; apply AG5; lia| lia| lia|].
apply (PMKA.u8_keepA RSEGS L ar LBc FF sp 14336 W14 M1 M4 EK14 WAPP14 FRB (op + 9) 0 (AOF (op + 9) 1 ltac:(lia) ltac:(lia))); [| exact C9].
intros i Hi r0 [<-|[]]. unfold L5.in_rng; cbn [fst snd]; lia.
+ rewrite <- VIS5 in C512. exact (proj1 (L5A.u32_at_vis H4 M5 (op + 12) 0 ltac:(eapply L5A.avis_sub; [exact OVIS4|lia|lia]) ltac:(lia) ltac:(lia)) C512).
+ apply (PMKA.vstr_keepA RSEGS L ar LBc FF sp 14336 W15 M1 M5 EK15 WAPP15 FRB BRB (op + 336) _ (AOF (op + 336) 24 ltac:(lia) ltac:(lia))); [| | | exact TB1].
* unfold PMSPA.pst_reset. cbn [PM.p_tb]. change (PM.p_tb s) with tb. rewrite vs_own_reset. intros x Hx. right. apply in_or_app. left. exact Hx.
* intros i Hi r0 [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia.
* intros c n p E i Hi r0 Hr. unfold PMSPA.pst_reset in E. cbn [PM.p_tb] in E. change (PM.p_tb s) with tb in E.
destruct (reset_tb_long tb c n p E) as (n' & E').
destruct (TBB c n' p E') as (X0 & _ & _ & _ & _ & _ & X & _).
destruct Hr as [<-|[<-|[]]]; unfold L5.in_rng; cbn [fst snd]; lia.
+ apply (PMFA.vec_at_agreeA RSEGS M4 M5 (op + 360) b k [PM.ps_root]); [lia|lia|lia|lia| | |exact VEC4].
* intros i Hi. apply AG5; lia.
* split; [intros i Hi; apply AG5; lia|]. intros x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
unfold BIGSHADOW_LO, BIGSHADOW_HI in SX. apply AG5; [lia| unfold nsh in OPN; lia].
-
change (PMSPA.o_tb PMA.AD fb) with (op + 336). change (PMSPA.o_vec PMA.AD fb) with (op + 360).
apply (L5SAR.ahpres_of L ar LBX FF sp 14336 Wsp M M5 EK05x).
+ pose proof ASTK5 as (_ & _ & _ & _ & D5 & _). exact D5.
+ exact (PMKA.dk_sublb L ar LBc LBX FF sp 14336 M M5 INCx DK05).
- apply (L5LZ.model_rt_trans model model4 model5); [|exact MRT5].
apply (L5LZ.model_rt_trans model model3 model4); [|exact MRT4].
apply (L5LZ.model_rt_trans model model2 model3); [|exact MRT3].
apply (L5LZ.model_rt_trans model model1 model2); [exact MRT1| exact MRT2].
- intros x Hx. apply INCLK2. apply INCLK4. exact Hx.
- intros x Hx. apply INCAw4. apply INCAw2. exact Hx.
- exact AM5.
- change (ri_inv HI ((b, 32 * 2 ^ k) :: (qc, 16384) :: PM.vs_own tb ++ LBX) FF LK4 cr Aw4 M5 (vml_of model5)) in HH5.
rewrite EPO. exact (PMARS1.ri_swap12 L ar C HI HIok _ _ _ _ _ _ _ _ _ HH5). }
assert (ZSUB : forall (Mx : word -> option byte) a n a' n', L5KA.zeros_at Mx a n -> a <= a' -> a' + n' <= a + n -> L5KA.zeros_at Mx a' n').
{ intros Mx a n a' n' Z X1 X2 i Hi. replace (a' + i) with (a + (a' - a + i)) by lia. apply Z. lia. }
assert (DIVop : forall j, 0 <= j -> (op + j) / 8 = op / 8 + j / 8).
{ intros j Hj. replace (op + j) with (j + (op / 8) * 8) by (pose proof (Z.div_mod op 8 ltac:(lia)); lia). rewrite Z.div_add by lia. lia. }
assert (Zop : L5KA.zeros_at MV (op / 8 + SB) (24 / 8)).
{ apply (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model op 24 HH (AOF op 24 ltac:(lia) ltac:(lia)) O8); [lia| reflexivity| exact PC0]. }
assert (Z320 : L5KA.zeros_at MV ((op + 320) / 8 + SB) (64 / 8)).
{ apply (PMKA.obj_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model (op + 320) 64 HH (AOF (op + 320) 64 ltac:(lia) ltac:(lia))); [| lia| reflexivity| exact PC320].
replace (op + 320) with (op + 40 * 8) by lia. rewrite Z_mod_plus_full. exact O8. }
rewrite (DIVop 320 ltac:(lia)) in Z320. change (320 / 8) with 40 in Z320. change (24 / 8) with 3 in Zop. change (64 / 8) with 8 in Z320.
assert (VO : forall a n, op <= a -> a + n <= op + 384 -> L5A.avis H a n) by (intros a n X1 X2; eapply L5A.avis_sub; [exact OVIS| lia| lia]).
assert (VWo : forall a n, op <= a -> a + n <= op + 384 -> 0 <= n -> L5.writable RSEGS MV a n).
{ intros a n X1 X2 X3. apply (proj2 (L5A.writable_vis H M a n (VO a n X1 X2) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M op 384); [exact PD| lia| lia]| lia| lia]. }
assert (VSW : L5.writable RSEGS MV (sp - 48) 48).
{ apply (proj2 (L5A.writable_vis H M (sp - 48) 48 (VIS (sp - 48) 48 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M (sp - 14336) 14336); [exact SDEF| lia| lia]| lia| lia]. }
assert (IC0 : L5.img_clear MV 1228800 1261568) by (apply L5A.img_clear_mrestrict; exact GOT).
assert (CSBv : L5.u64_at RSEGS MV 1289464 2147450880) by (apply (proj2 (L5A.u64_at_vis H M 1289464 2147450880 (VIMG 1289464 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CSB).
assert (CUARv : L5.u32_at RSEGS MV 1289472 1) by (apply (proj2 (L5A.u32_at_vis H M 1289472 1 (VIMG 1289472 4 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact CUAR).
assert (V0v : L5.u64_at RSEGS MV (op + 360) b) by (apply (proj2 (L5A.u64_at_vis H M (op + 360) b (VO (op + 360) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact V0).
assert (V8v : L5.u64_at RSEGS MV (op + 368) (b + 32 * Z.of_nat (length stk))).
{ replace (op + 368) with (op + 360 + 8) by lia. apply (proj2 (L5A.u64_at_vis H M (op + 360 + 8) _ (VO (op + 360 + 8) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact V8. }
assert (LS : 0 <= 32 * Z.of_nat (length stk) <= 65536) by lia.
assert (HOFFs := HOFF).
assert (SRV : forall d, 0 <= d < 2 ^ 63 -> v_srai (Z_to_bv 64 d) (bv_unsigned (5%bv : bv 6)) = Z_to_bv 64 (d / 32)).
{ intros d Hd. change (bv_unsigned (5%bv : bv 6)) with 5. apply PMARS1.v_srai5_small. exact Hd. }
assert (R11 : (11%bv : bv 5) <> 0%bv) by (intros X; discriminate X).
clear FAb FAq.
case_eq tb; [intros n ETB| intros c n p ETB].
-
assert (PTB' := PTB). rewrite ETB in PTB'. destruct PTB' as (TD & TC & Hn & T0).
assert (T0v : L5.u8_at RSEGS MV (op + 336) (2 * n)) by (apply (proj2 (L5A.u8_at_vis H M (op + 336) _ (VO (op + 336) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact T0).
assert (EVEN : Z.testbit (2 * n) 0 = false) by (rewrite Z.bit0_odd; rewrite Z.odd_mul; reflexivity).
pose proof (PMARSP.arsS_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => 2 * n | 34%nat => b | 36%nat => b + 32 * Z.of_nat (length stk) | _ => 0 end)) as P.
cbn beta iota in P. rewrite HO in P.
assert (Q1 : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
assert (Q2 : 0 <= 2 * n < 2 ^ 64) by (clear - Hn; lia).
assert (Q3 : 0 <= b < 2 ^ 64) by (clear - Bb0 Bb47 P2k; lia).
assert (Q4 : 0 <= b + 32 * Z.of_nat (length stk) < 2 ^ 64) by (clear - Bb0 Bb47 Hlen P2k; lia).
assert (Q9 : 140735332487216 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
assert (Q12 : 6885376 <= op <= 140737488354944) by (clear - O1 O3; lia).
assert (Q14 : 2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) by (clear - OPN; unfold nsh in OPN; lia).
assert (Q15 : L5KA.zeros_at MV ((op / 8) + 2147450881) 1) by (apply (ZSUB MV (op / 8 + SB) 3); [exact Zop| unfold SB; lia| unfold SB; lia]).
assert (Q16 : L5KA.zeros_at MV ((op / 8) + 2147450922) 6) by (apply (ZSUB MV (op / 8 + 40 + SB) 8); [exact Z320| unfold SB; lia| unfold SB; lia]).
assert (Q17 : L5KA.zeros_at MV (((op + 9) / 8) + 2147450880) 1).
{ rewrite (DIVop 9 ltac:(lia)). change (9 / 8) with 1. apply (ZSUB MV (op / 8 + SB) 3); [exact Zop| unfold SB; lia| unfold SB; lia]. }
assert (Q18 : L5KA.zeros_at MV (((op + 12) / 8) + 2147450880) 1).
{ rewrite (DIVop 12 ltac:(lia)). change (12 / 8) with 1. apply (ZSUB MV (op / 8 + SB) 3); [exact Zop| unfold SB; lia| unfold SB; lia]. }
assert (Q19 : L5KA.zeros_at MV (((op + 337) / 8) + 2147450880) 1).
{ rewrite (DIVop 337 ltac:(lia)). change (337 / 8) with 42. apply (ZSUB MV (op / 8 + 40 + SB) 8); [exact Z320| unfold SB; lia| unfold SB; lia]. }
assert (Q20 : (sp - 48) + 48 <= op \/ op + 384 <= (sp - 48)) by (clear - OPS; lia).
assert (Q22 : 0 <= 2 * n <= 255) by (clear - Hn; lia).
assert (Q25 : 4096 <= b <= 140737488355328) by (clear - Bb0 Bb47; lia).
assert (Q28 : 0 <= (b + 32 * Z.of_nat (length stk)) - b <= 65536) by (clear - LS; lia).
assert (Q29 : PMARSP.aligned ((b + 32 * Z.of_nat (length stk)) - b) 32).
{ unfold PMARSP.aligned. replace ((b + 32 * Z.of_nat (length stk)) - b) with (Z.of_nat (length stk) * 32) by lia. apply Z_mod_mult. }
assert (Q30 : L5.writable RSEGS MV (op + 8) 2) by (apply VWo; lia).
assert (Q31 : L5.writable RSEGS MV (op + 336) 2) by (apply VWo; lia).
assert (Q32 : L5.writable RSEGS MV (op + 368) 8) by (apply VWo; lia).
L5SAR.feed P ltac:(first [assumption | unfold PMARSP.aligned; assumption]).
clear Q2 Q3 Q4 Q14 Q15 Q16 Q17 Q18 Q19 Q22 Q25 Q28 Q29 Q30 Q31.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A12 & A18 & A19 & A110 & A111 & A112 & A113 & A118 & C336 & C337 & C9 & C8 & C32 & C24 & C16 & C8s & C368).
pose proof (PMARS1.srai_to fx1 R1 M1v 0xac09c (ltac:(oW' 0xac09c%Z)) _ _ _ (ltac:(oF' 0xac09c%Z)) eq_refl (ltac:(oD' 0xac09c%Z)) eq_refl ltac:(lia) ltac:(lia)) as MSR.
set (R1t := regupd R1 11%bv (v_srai (getr R1 10%bv) (bv_unsigned (5%bv : bv 6)))) in MSR.
assert (E10 : getr R1 10%bv = Z_to_bv 64 (32 * Z.of_nat (length stk))) by (rewrite L5K.rl10, A110; f_equal; lia).
assert (T11 : getr R1t (reg 11) = Z_to_bv 64 (Z.of_nat (length stk))).
{ unfold R1t. rewrite <- L5K.rl11. rewrite (getr_same R1 11%bv _ R11). rewrite E10. rewrite SRV by lia. f_equal.
rewrite Z.mul_comm. apply Z.div_mul. lia. }
assert (TO : forall j, j <> 11%nat -> (j < 32)%nat -> getr R1t (reg j) = getr R1 (reg j)).
{ intros j Hj Hl. unfold R1t. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E.
rewrite Z.mod_small in E by lia. lia. }
pose proof (PMARSP.arsT_conc fx1 R1t M1v (fun j => match j with 2%nat => sp | 40%nat => op | _ => 0 end)) as P. cbn beta iota in P.
assert (U0 : 0 <= op < 2 ^ 64) by (clear - Q12; lia).
assert (U2 : getr R1t (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (TO 2%nat) by lia; exact A12).
assert (U8 : getr R1t (reg 8) = Z_to_bv 64 op) by (rewrite (TO 8%nat) by lia; rewrite A18; exact A10).
assert (U9 : getr R1t (reg 9) = Z_to_bv 64 (op + 360)) by (rewrite (TO 9%nat) by lia; exact A19).
assert (U18 : getr R1t (reg 18) = Z_to_bv 64 2147450880) by (rewrite (TO 18%nat) by lia; exact A118).
assert (U11 : L5.writable RSEGS M1v (sp - 48) 48) by exact (L5.writable_grows RSEGS MV M1v (sp - 48) 48 MG1 VSW).
assert (U13 : L5.writable RSEGS M1v (op + 368) 8) by exact (L5.writable_grows RSEGS MV M1v (op + 368) 8 MG1 Q32).
L5SAR.feed P ltac:(first [assumption | unfold PMARSP.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & A2ra & A2a0 & C368'). clear Q20.
unfold PMSPA.cfg. cbn [pa_reset ADDR_A].
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xabf84 R2 0xaa778 M2v
(fun a => (sp - 32 <= a < sp - 32 + 32) \/ (op + 8 <= a < op + 8 + 2) \/ (op + 336 <= a < op + 336 + 2) \/ (op + 368 <= a < op + 368 + 8)) K HH AM).
{ eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MSR| exact MS2]]. }
{ intros x Hx. apply MG2. apply MG1. exact Hx. }
{ intros a Ha Hnw. rewrite FRZ2; [| exact Ha| intros X; apply Hnw; right; right; right; exact X].
apply FRZ1; [exact Ha| intros X; apply Hnw; left; exact X| intros X; apply Hnw; right; left; exact X| intros X; apply Hnw; right; right; left; exact X
| intros X; apply Hnw; right; right; right; exact X]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|[X|X]]]; unfold aclientw, aclient_g.
+ right; left. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
- destruct Wa as [X|[X|[X|X]]]; lia. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M2v) in VIS1.
assert (B64 : forall a v, ((ahl_ceil ar <= a /\ a + 8 <= 2 ^ 47) \/ (op <= a /\ a + 8 <= op + 384)) -> ~ (op + 368 <= a + 7 /\ a < op + 376) ->
L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha Na X. assert (VA : L5A.avis H a 8) by (destruct Ha as [Y|Y]; [apply VIS; lia| apply VO; lia]).
apply (proj1 (L5A.u64_at_vis H M1 a v VA ltac:(lia) ltac:(lia))). rewrite VIS1.
apply (L5C.u64_at_agree RSEGS M1v M2v); [intros i Hi; apply FRZ2; [lia| intros Y; apply Na; lia]| lia| lia| exact X]. }
assert (B8 : forall a v, op <= a < op + 368 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v).
{ intros a v Ha X. apply (proj1 (L5A.u8_at_vis H M1 a v (VO a 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1.
apply (L5C.u8_at_agree RSEGS M1v M2v); [intros i Hi; apply FRZ2; [lia| intros Y; lia]| lia| lia| exact X]. }
assert (SH1 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh M M1 a0 n0).
{ intros a0 n0 Ha Hn0 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
apply FR1; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| intros [Y|[Y|[Y|Y]]]].
- clear - Y SX SLO SPT. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX. lia.
- exact (nsh_not op 384 (S x) OPN ltac:(lia) SX).
- exact (nsh_not op 384 (S x) OPN ltac:(lia) SX).
- exact (nsh_not op 384 (S x) OPN ltac:(lia) SX). }
apply (TAIL fx2 R2 M1 model1 _ HH1 AM1 MRT1 MGM1 FR1).
{ intros a [X|[X|[X|X]]]; [left; lia| right; left; lia| right; right; left; lia| right; right; right; left; lia]. }
{ exact A2ra. }
{ rewrite (KS2 2%nat) by inl. exact U2. }
{ rewrite (KS2 8%nat) by inl. exact U8. }
{ rewrite (KS2 9%nat) by inl. exact U9. }
{ exact A2a0. }
{ rewrite (KS2 11%nat) by inl. exact T11. }
{ rewrite (KS2 18%nat) by inl. exact U18. }
{ intros j Hj. repeat (destruct Hj as [<-|Hj]; [rewrite (KS2 _) by inl; rewrite TO by lia; rewrite (KS1 _) by inl; reflexivity|]). destruct Hj. }
{ apply B64; [left; lia| lia| exact C8s]. }
{ apply B64; [left; lia| lia| exact C16]. }
{ apply B64; [left; lia| lia| exact C24]. }
{ apply B64; [left; lia| lia| exact C32]. }
{ apply B8; [lia| exact C8]. }
{ apply B8; [lia| exact C9]. }
{ apply (proj1 (L5A.u64_at_vis H M1 (op + 368) b (VO (op + 368) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1.
rewrite (TO 12%nat) in C368' by lia. rewrite A112 in C368'. rewrite L5.unsigned_lit in C368' by lia. exact C368'. }
{ unfold PMSPA.pst_reset. cbn [PM.p_tb]. change (PM.p_tb s) with tb. rewrite ETB.
split; [exact (L5.defined_grows M M1 (op + 336) 24 MGM1 TD)|]. split; [apply (PMFA.accA_agree M M1); [apply SH1; lia| exact TC]|].
split; [lia|]. change (2 * 0) with 0. apply B8; [lia| exact C336]. }
-
assert (PTB' := PTB). rewrite ETB in PTB'. destruct PTB' as (TD & TC & T0 & T8 & T16 & Hnc & Hc & Hce & TDp & TCp).
destruct (TBB c n p ETB) as (Pc & Pp0 & Pp16 & Pp47 & PN & Pceil & Pfb & _ & _ & PinC).
assert (Ip : In (p, c) (PM.parser_own s ++ LBX)) by (apply in_or_app; left; exact (ITB c n p ETB)).
pose proof (WB _ Ip) as ((Y0 & Y1 & Y2 & Y3 & Y4 & Y5) & _). cbn [fst snd] in Y0, Y1, Y2, Y3, Y4, Y5.
rewrite (L5A.aly_img_lo L C LYa), (L5A.aly_img_hi L C LYa) in Y1. clear Y5.
assert (YIMG : ~ (0x10000 <= p < 0x691000)) by (clear - Y1 Pc; lia). clear Y1.
assert (Q24e : (p + 1 <= op \/ op + 384 <= p)) by (clear - Pfb Eop Pc; lia).
assert (PnO : forall i, p <= i < p + 1 -> ~ (op <= i < op + 384)) by (clear - Pfb Eop Pc; intros i Hi X; lia). clear Pfb.
assert (T0b : L5.u8_at RSEGS M (op + 336) ((c + 1) mod 256)) by exact (PMF.u8_of_u64 RSEGS M (op + 336) (c + 1) ltac:(lia) T0).
assert (T0v : L5.u8_at RSEGS MV (op + 336) ((c + 1) mod 256)) by (apply (proj2 (L5A.u8_at_vis H M (op + 336) _ (VO (op + 336) 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))); exact T0b).
assert (T16v : L5.u64_at RSEGS MV (op + 352) p).
{ replace (op + 352) with (op + 336 + 16) by lia. apply (proj2 (L5A.u64_at_vis H M (op + 336 + 16) p (VO (op + 336 + 16) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). exact T16. }
assert (ODB : Z.testbit ((c + 1) mod 256) 0 = true) by exact (PMF.odd_byte c Hce ltac:(lia)).
assert (ZP : L5KA.zeros_at MV (p / 8 + SB) (8 / 8)).
{ apply (PMKA.blk_shadow_vis L ar C HI LYa HIok _ FF LK cr Aw M model p c p 8 HH Ip); [lia| lia| apply PMKA.mod16_8'; exact Pp16| lia| reflexivity|].
intros a Ha. apply TCp. lia. }
change (8 / 8) with 1 in ZP.
assert (WPv : L5.writable RSEGS MV p 1).
{ apply (proj2 (L5A.writable_vis H M p 1 (VBLK p c p 1 Ip ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))).
apply (L5C.writable_of_defined RSEGS); [apply (L5.defined_sub M p c); [exact TDp| lia| lia]| lia| lia]. }
pose proof (PMARSP.arsL_conc fx R MV (fun j => match j with 2%nat => sp | 33%nat => (c + 1) mod 256 | 34%nat => b | 36%nat => b + 32 * Z.of_nat (length stk)
| 37%nat => p | _ => 0 end)) as P.
cbn beta iota in P. rewrite HO in P.
assert (Q1 : 0 <= sp < 2 ^ 64) by (clear - SLO SHI SPT; lia).
assert (Q2 : 0 <= (c + 1) mod 256 < 2 ^ 64) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
assert (Q3 : 0 <= b < 2 ^ 64) by (clear - Bb0 Bb47 P2k; lia).
assert (Q4 : 0 <= b + 32 * Z.of_nat (length stk) < 2 ^ 64) by (clear - Bb0 Bb47 Hlen P2k; lia).
assert (Q5 : 0 <= p < 2 ^ 64) by (clear - Pp0 Pp47 Pc; lia).
assert (Q9 : 140735332487216 <= sp <= 140737488355328) by (clear - SLO SHI SPT; lia).
assert (Q12 : 6885376 <= op <= 140737488354944) by (clear - O1 O3; lia).
assert (Q14 : 2147446784 + 17592186048512 <= op \/ op + 384 <= 2147446784) by (clear - OPN; unfold nsh in OPN; lia).
assert (Q15 : L5KA.zeros_at MV ((op / 8) + 2147450881) 1) by (apply (ZSUB MV (op / 8 + SB) 3); [exact Zop| unfold SB; lia| unfold SB; lia]).
assert (Q16 : L5KA.zeros_at MV ((op / 8) + 2147450922) 6) by (apply (ZSUB MV (op / 8 + 40 + SB) 8); [exact Z320| unfold SB; lia| unfold SB; lia]).
assert (Q17 : L5KA.zeros_at MV (((op + 9) / 8) + 2147450880) 1).
{ rewrite (DIVop 9 ltac:(lia)). change (9 / 8) with 1. apply (ZSUB MV (op / 8 + SB) 3); [exact Zop| unfold SB; lia| unfold SB; lia]. }
assert (Q18 : L5KA.zeros_at MV (((op + 12) / 8) + 2147450880) 1).
{ rewrite (DIVop 12 ltac:(lia)). change (12 / 8) with 1. apply (ZSUB MV (op / 8 + SB) 3); [exact Zop| unfold SB; lia| unfold SB; lia]. }
assert (Q19 : L5KA.zeros_at MV (((op + 337) / 8) + 2147450880) 1).
{ rewrite (DIVop 337 ltac:(lia)). change (337 / 8) with 42. apply (ZSUB MV (op / 8 + 40 + SB) 8); [exact Z320| unfold SB; lia| unfold SB; lia]. }
assert (Q20 : (sp - 48) + 48 <= op \/ op + 384 <= (sp - 48)) by (clear - OPS; lia).
assert (Q22 : 0 <= (c + 1) mod 256 <= 255) by (pose proof (Z.mod_pos_bound (c + 1) 256 ltac:(lia)); lia).
assert (Q23 : 4096 <= p <= 140737488355320) by (clear - Pp0 Pp47 Pc; lia).
assert (Q24 : PMARSP.aligned p 8) by (unfold PMARSP.aligned; apply PMKA.mod16_8'; exact Pp16).
assert (Q24b : 2147446784 + 17592186048512 <= p \/ p + 1 <= 2147446784) by (clear - PN Pc; unfold nsh in PN; lia).
assert (Q24c : L5KA.zeros_at MV ((p / 8) + 2147450880) 1) by exact ZP.
assert (Q24d : ((sp - 48) + 48 <= p \/ p + 1 <= (sp - 48))) by (clear - Pceil SLO Pc; lia).
assert (Q25 : 4096 <= b <= 140737488355328) by (clear - Bb0 Bb47; lia).
assert (Q28 : 0 <= (b + 32 * Z.of_nat (length stk)) - b <= 65536) by (clear - LS; lia).
assert (Q29 : PMARSP.aligned ((b + 32 * Z.of_nat (length stk)) - b) 32).
{ unfold PMARSP.aligned. replace ((b + 32 * Z.of_nat (length stk)) - b) with (Z.of_nat (length stk) * 32) by lia. apply Z_mod_mult. }
assert (Q30 : L5.writable RSEGS MV (op + 8) 2) by (apply VWo; lia).
assert (Q31 : L5.writable RSEGS MV (op + 344) 8) by (apply VWo; lia).
assert (Q32 : L5.writable RSEGS MV (op + 368) 8) by (apply VWo; lia).
L5SAR.feed P ltac:(first [assumption | unfold PMARSP.aligned; assumption]).
clear Q2 Q3 Q4 Q5 Q14 Q15 Q16 Q17 Q18 Q19 Q22 Q23 Q24 Q24b Q24c Q24d Q24e Q25 Q28 Q29 Q30 Q31.
destruct P as (fx1 & R1 & M1v & MG1 & _ & FRZ1 & MS1 & KS1 & A12 & A18 & A19 & A110 & A111 & A112 & A118 & C344 & C0p & C9 & C8 & C32 & C24 & C16 & C8s & C368).
pose proof (PMARS1.srai_to fx1 R1 M1v 0xac09c (ltac:(oW' 0xac09c%Z)) _ _ _ (ltac:(oF' 0xac09c%Z)) eq_refl (ltac:(oD' 0xac09c%Z)) eq_refl ltac:(lia) ltac:(lia)) as MSR.
set (R1t := regupd R1 11%bv (v_srai (getr R1 10%bv) (bv_unsigned (5%bv : bv 6)))) in MSR.
assert (E10 : getr R1 10%bv = Z_to_bv 64 (32 * Z.of_nat (length stk))) by (rewrite L5K.rl10, A110; f_equal; lia).
assert (T11 : getr R1t (reg 11) = Z_to_bv 64 (Z.of_nat (length stk))).
{ unfold R1t. rewrite <- L5K.rl11. rewrite (getr_same R1 11%bv _ R11). rewrite E10. rewrite SRV by lia. f_equal.
rewrite Z.mul_comm. apply Z.div_mul. lia. }
assert (TO : forall j, j <> 11%nat -> (j < 32)%nat -> getr R1t (reg j) = getr R1 (reg j)).
{ intros j Hj Hl. unfold R1t. apply getr_other. intros E. apply Hj. apply (f_equal (@bv_unsigned 5)) in E.
rewrite Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E. change (bv_unsigned (11%bv : bv 5)) with 11 in E.
rewrite Z.mod_small in E by lia. lia. }
pose proof (PMARSP.arsT_conc fx1 R1t M1v (fun j => match j with 2%nat => sp | 40%nat => op | _ => 0 end)) as P. cbn beta iota in P.
assert (U0 : 0 <= op < 2 ^ 64) by (clear - Q12; lia).
assert (U2 : getr R1t (reg 2) = Z_to_bv 64 (sp - 48)) by (rewrite (TO 2%nat) by lia; exact A12).
assert (U8 : getr R1t (reg 8) = Z_to_bv 64 op) by (rewrite (TO 8%nat) by lia; rewrite A18; exact A10).
assert (U9 : getr R1t (reg 9) = Z_to_bv 64 (op + 360)) by (rewrite (TO 9%nat) by lia; exact A19).
assert (U18 : getr R1t (reg 18) = Z_to_bv 64 2147450880) by (rewrite (TO 18%nat) by lia; exact A118).
assert (U11 : L5.writable RSEGS M1v (sp - 48) 48) by exact (L5.writable_grows RSEGS MV M1v (sp - 48) 48 MG1 VSW).
assert (U13 : L5.writable RSEGS M1v (op + 368) 8) by exact (L5.writable_grows RSEGS MV M1v (op + 368) 8 MG1 Q32).
L5SAR.feed P ltac:(first [assumption | unfold PMARSP.aligned; assumption]).
destruct P as (fx2 & R2 & M2v & MG2 & _ & FRZ2 & MS2 & KS2 & A2ra & A2a0 & C368'). clear Q20.
unfold PMSPA.cfg. cbn [pa_reset ADDR_A].
apply (L5SAR.apiece L ar C HI LYa HIok _ FF LK cr Aw M model fx fx2 R 0xabf84 R2 0xaa778 M2v
(fun a => (sp - 32 <= a < sp - 32 + 32) \/ (op + 8 <= a < op + 8 + 2) \/ (p + 0 <= a < p + 0 + 1) \/ (op + 344 <= a < op + 344 + 8)
\/ (op + 368 <= a < op + 368 + 8)) K HH AM).
{ eapply msteps_trans; [exact MS1| eapply msteps_trans; [exact MSR| exact MS2]]. }
{ intros x Hx. apply MG2. apply MG1. exact Hx. }
{ intros a Ha Hnw. rewrite FRZ2; [| exact Ha| intros X; apply Hnw; right; right; right; right; exact X].
apply FRZ1; [exact Ha| intros X; apply Hnw; left; exact X| intros X; apply Hnw; right; left; exact X| intros X; apply Hnw; right; right; left; exact X
| intros X; apply Hnw; right; right; right; left; exact X| intros X; apply Hnw; right; right; right; right; exact X]. }
{ intros a Ha Wa. split.
- destruct Wa as [X|[X|[X|[X|X]]]]; unfold aclientw, aclient_g.
+ right; left. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
+ left. exists (p, c). split; [exact Ip| cbn [fst snd]; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
+ do 3 right; left. exists (fb, 4, rs). split; [exact Hfb|]. cbn [ff_addr ff_class fst snd]. change (ff_bytes 4) with 1024. split; [lia| intros Y; lia].
- destruct Wa as [X|[X|[X|[X|X]]]]; [lia| lia| intros Y; apply YIMG; lia| lia| lia]. }
intros M1 model1 HH1 AM1 MRT1 HID1 VIS1 MGM1 FR1 VV1. change (mrestrict H M1 = M2v) in VIS1.
assert (B64 : forall a v, ((ahl_ceil ar <= a /\ a + 8 <= 2 ^ 47) \/ (op <= a /\ a + 8 <= op + 384)) -> ~ (op + 368 <= a + 7 /\ a < op + 376) ->
L5.u64_at RSEGS M1v a v -> L5.u64_at RSEGS M1 a v).
{ intros a v Ha Na X. assert (VA : L5A.avis H a 8) by (destruct Ha as [Y|Y]; [apply VIS; lia| apply VO; lia]).
apply (proj1 (L5A.u64_at_vis H M1 a v VA ltac:(lia) ltac:(lia))). rewrite VIS1.
apply (L5C.u64_at_agree RSEGS M1v M2v); [intros i Hi; apply FRZ2; [lia| intros Y; apply Na; lia]| lia| lia| exact X]. }
assert (B8 : forall a v, op <= a < op + 368 -> L5.u8_at RSEGS M1v a v -> L5.u8_at RSEGS M1 a v).
{ intros a v Ha X. apply (proj1 (L5A.u8_at_vis H M1 a v (VO a 1 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1.
apply (L5C.u8_at_agree RSEGS M1v M2v); [intros i Hi; apply FRZ2; [lia| intros Y; lia]| lia| lia| exact X]. }
assert (SH1 : forall a0 n0, 0 <= a0 -> a0 + n0 <= 2 ^ 47 -> PMFA.agsh M M1 a0 n0).
{ intros a0 n0 Ha Hn0 x Hx. pose proof (PMKA.S_in_shadow x ltac:(lia)) as SX.
apply FR1; [unfold BIGSHADOW_LO, BIGSHADOW_HI in SX; lia| intros [Y|[Y|[Y|[Y|Y]]]]].
- clear - Y SX SLO SPT. unfold BIGSHADOW_LO, BIGSHADOW_HI in SX. lia.
- exact (nsh_not op 384 (S x) OPN ltac:(lia) SX).
- exact (nsh_not p c (S x) PN ltac:(lia) SX).
- exact (nsh_not op 384 (S x) OPN ltac:(lia) SX).
- exact (nsh_not op 384 (S x) OPN ltac:(lia) SX). }
assert (AG1 : forall a0 n0, op + 336 <= a0 -> a0 + n0 <= op + 344 \/ (op + 352 <= a0 /\ a0 + n0 <= op + 360) -> L5C.agree_on M M1 a0 n0).
{ intros a0 n0 H1 H2 i Hi. apply FR1; [lia| intros [Y|[Y|[Y|[Y|Y]]]]; [lia| lia| apply (PnO i); lia| lia| lia]]. }
apply (TAIL fx2 R2 M1 model1 _ HH1 AM1 MRT1 MGM1 FR1).
{ intros a [X|[X|[X|[X|X]]]]; [left; lia| right; left; lia| right; right; right; right; exists c, n, p; split; [exact ETB| lia]
| right; right; left; lia| right; right; right; left; lia]. }
{ exact A2ra. }
{ rewrite (KS2 2%nat) by inl. exact U2. }
{ rewrite (KS2 8%nat) by inl. exact U8. }
{ rewrite (KS2 9%nat) by inl. exact U9. }
{ exact A2a0. }
{ rewrite (KS2 11%nat) by inl. exact T11. }
{ rewrite (KS2 18%nat) by inl. exact U18. }
{ intros j Hj. repeat (destruct Hj as [<-|Hj]; [rewrite (KS2 _) by inl; rewrite TO by lia; rewrite (KS1 _) by inl; reflexivity|]). destruct Hj. }
{ apply B64; [left; lia| lia| exact C8s]. }
{ apply B64; [left; lia| lia| exact C16]. }
{ apply B64; [left; lia| lia| exact C24]. }
{ apply B64; [left; lia| lia| exact C32]. }
{ apply B8; [lia| exact C8]. }
{ apply B8; [lia| exact C9]. }
{ apply (proj1 (L5A.u64_at_vis H M1 (op + 368) b (VO (op + 368) 8 ltac:(lia) ltac:(lia)) ltac:(lia) ltac:(lia))). rewrite VIS1.
rewrite (TO 12%nat) in C368' by lia. rewrite A112 in C368'. rewrite L5.unsigned_lit in C368' by lia. exact C368'. }
{ unfold PMSPA.pst_reset. cbn [PM.p_tb]. change (PM.p_tb s) with tb. rewrite ETB.
split; [exact (L5.defined_grows M M1 (op + 336) 24 MGM1 TD)|]. split; [apply (PMFA.accA_agree M M1); [apply SH1; lia| exact TC]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; lia| lia| lia| exact T0]|].
split; [replace (op + 336 + 8) with (op + 344) by lia; apply B64; [right; lia| lia| exact C344]|].
split; [apply (L5C.u64_at_agree RSEGS M M1); [apply AG1; lia| lia| lia| exact T16]|].
split; [lia|]. split; [lia|]. split; [exact Hce|].
split; [exact (L5.defined_grows M M1 p c MGM1 TDp)| apply (PMFA.accA_agree M M1); [apply SH1; lia| exact TCp]]. }
Qed.
End WithHeap.
End PMARS.
