(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib Require Import PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.LibA Require Import ExecF ITreeA StepF SysStepF.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.AsanW Require Import AImg AProto ABase ABytes ASecFacts AMalloc_iface ADepot_iface ARep ALayout AHeapP ARepKit ARepFrame ARepExt ARepExt2
AKit AKit2 AModelFacts APrimFacts F_apoison F_aalloc1 F_aalloc2 F_aalloc F_amalloc_icpt F_amalloc_pre F_aalloc2g F_aalloc3g F_amalloc_tailg F_amalloc_arep
ARepStore ARepStoreG ARefill_iface ARefillP ACallocG.
From OSSVerify.Proofs.zstd.fse_read_ncount.lib.Common Require Import RunDraw.
Import ListNotations.
Import Exc.
(* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_orc_old ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.LiaTuning.lia_k12.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.slia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.slia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.flia ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.flia_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.zrange_nonneg ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.zrange_nonneg_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Step.solve_load ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.solve_load_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.word_eq_tac_k12.
Local Ltac OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes ::= OSSVerify.Proofs.zstd.fse_read_ncount.lib.Lib.Tac.simpl_arr_sizes_k12.
(* [comment removed for export] *)

Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Section CANSEC1. Context {rc : runConstT}.
#[using="Type"] Local Lemma aobj_int : forall a n, aobj a n -> 0x10000 <= n ->
6254592 <= a /\ a + n <= ATOP /\ exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof.
intros a n H Hn. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040>25807118408.1036002021247.103826536157.10 48752954456.1000000600:00D00MS2H21HS2H3S2H22H52HnS2H31H2H0".
split; [lia|]. split; [lia|]. destruct H4; [exists 0 | exists 1]; lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Local Lemma aobj4_int : forall a, aobj a 4096 ->
4096 <= a /\ a + 4096 <= ATOP
/\ (exists k, 0 <= k <= 1 /\ a + 4096 <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a)
/\ (exists j, 0 <= j <= 1 /\ a + 4096 <= 65536 + j * 18446744073709551616 /\ 6254592 * j <= a).
Proof.
intros a H. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in H. pose proof atop_range. destruct H as (H1 & H2 & H3 & H4 & H5).
Local Ltac2 Set LiaHints.tbl := fun () => "0040=25807118408.836072040845.83826536157.8 48752954456.800000900=00A00MS2H21H2H5S2H3S2H2S2H31H2H02H5".
split; [lia|]. split; [lia|]. split; [destruct H4; [exists 0 | exists 1]; lia | destruct H5 as [_ [H5|H5]]; [exists 0 | exists 1]; lia].
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
Local Ltac dlia := repeat match goal with |- _ /\ _ => split end; first [exact I | lia].
#[using="Type"] Lemma amalloc_prim_eq : forall RESV st n c,
1 <= n -> is_primary n = true -> class_id (needed_size n) = c ->
amalloc ATOP RESV st n =
cache_alloc st c (fun st1 (ok : bool) =>
if ok then SRet (set_next (N.succ (a_next st1)) (set_live (<[ a_next st1 := CPrim c n ]> (a_live st1)) st1), Some (a_next st1))
else SRet (st1, None)).
Proof.
intros RESV st n c N PRIM HC. pose proof (prim_facts n N PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
unfold amalloc.
Local Ltac2 Set LiaHints.tbl := fun () => "0020>30678964801.1631111599959.1600000@00ES2NS3RZR3RSR3NSRS3NSR".
replace (2 ^ 40 <? n) with false by (symmetry; apply Z.ltb_ge; lia).
replace (2 ^ 40 <? needed_size n) with false by (symmetry; apply Z.ltb_ge; lia). cbn [orb].
rewrite PRIM, HC. reflexivity.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma slot_carveG : forall m AB S n rz,
junk_at m AB S -> (rz = 16 \/ 32 <= rz) -> 0 <= n -> rz + n <= S ->
exists b0 b1 szh szl ctxj uj (j1 j2 : word),
rw_cells asegs m (AB + rz + -16) [C1 (Z_to_bv 8 b0); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 szh); C4 (Z_to_bv 64 szl); C8 (Z_to_bv 64 ctxj)]
/\ 0 <= b1 < 256
/\ rw_cells asegs m (AB + rz) [CB (Z.to_nat n) uj]
/\ (16 < rz -> rw_cells asegs m AB [C8 j1; C8 j2] /\ junk_at m (AB + 16) (rz - 32))
/\ junk_at m (AB + rz + n) (S - rz - n).
Proof.
intros m AB S n rz JK RZ N FIT.
destruct (Z.eq_dec rz 16) as [->|NE].
- Local Ltac2 Set LiaHints.tbl := fun () => "00G0>12394309023.3212736881841.1812812235460.1422497737964.1222498063434.9 2425313765.18 2425314019.11 35331230288.1637808469353.2252987684622.1858370173780.9 58370499570.1259314873579.2361079141220.1663257850714.1464196845615.3265499905964.1265500100362.9 65501989804.1665658656799.1166756559593.1167864076866.1467976741498.1100000100200700800900<00?00F00G00L00S00^00a00b00i00j00k00l00m01401501601;SSS3RZ2SSS1NS1NS1N3FITSS3FITS1N3FITS1N3FIT3RZ2S1HSS1N3FITSSSSS2RZ2NESSS3FIT".
destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [HJ R1].
destruct (junk_split m (AB + 16) n (S - 16 - n) ltac:(replace (n + (S - 16 - n)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
destruct (hdr_of_junk m AB HJ) as (b0 & b1 & szh & szl & ctxj & HDR & B0 & B1).
exists b0, b1, szh, szl, ctxj, uj, w0, w0.
replace (AB + 16 + -16) with AB by lia. split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|].
split; [intros; exfalso; lia|]. exact TL.
- assert (RZ2 : 32 <= rz) by lia.
destruct (junk_split m AB 16 (S - 16) ltac:(replace (16 + (S - 16)) with S by lia; exact JK) ltac:(lia) ltac:(lia)) as [LHJ R1].
destruct (junk_split m (AB + 16) (rz - 32) (S - rz + 16) ltac:(replace (rz - 32 + (S - rz + 16)) with (S - 16) by lia; exact R1) ltac:(lia) ltac:(lia)) as [MID R2].
destruct (junk_split m (AB + 16 + (rz - 32)) 16 (S - rz) ltac:(replace (16 + (S - rz)) with (S - rz + 16) by lia; exact R2) ltac:(lia) ltac:(lia)) as [HJ R3].
destruct (junk_split m (AB + 16 + (rz - 32) + 16) n (S - rz - n) ltac:(replace (n + (S - rz - n)) with (S - rz) by lia; exact R3) ltac:(lia) ltac:(lia)) as [[uj UJ] TL].
destruct (hdr_of_junk m _ HJ) as (b0 & b1 & szh & szl & ctxj & HDR & B0 & B1).
destruct (c8c8_of_junk m AB LHJ) as (j1 & j2 & LH).
exists b0, b1, szh, szl, ctxj, uj, j1, j2.
replace (AB + 16 + (rz - 32)) with (AB + rz + -16) in HDR by lia.
replace (AB + 16 + (rz - 32) + 16) with (AB + rz) in UJ, TL by lia.
split; [exact HDR|]. split; [exact B1|]. split; [exact UJ|]. split; [intros _; split; [exact LH| exact MID]|]. exact TL.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma malloc_post_gen_shift : forall DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 m1 ms',
malloc_post_gen DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m1 ms' ->
munch [(bv_unsigned sp - 4096, bv_unsigned sp); (t + 208 + c * 80, t + 208 + c * 80 + 4); (t + 2784, t + 2792)]%Z m0 m1 -> wmono asegs m0 m1 ->
malloc_post_gen DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n t c cnt AB UB PG pgw lo b1 maxc csz uj m0 ms'.
Proof.
intros until ms'. intros PM MU0 WM0. unfold malloc_post_gen in *.
destruct PM as (id & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & sj' & stj' & E & MU & REST).
exists id, t0, t1, t2, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m', sj', stj'. split; [exact E|]. split; [| split; [eapply wmono_trans; [exact WM0 | exact (proj1 REST)] | exact (proj2 REST)]].
eapply munch_trans; [eapply munch_weaken; [| exact MU0] | exact MU]. unfold sub_fp. cbn [outside]. intros q Hq. Local Ltac2 Set LiaHints.tbl := fun () => "0010>28573890679.62000009S4REST2Hq".
lia.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="Type"] Lemma amalloc_post_shiftG : forall CI AHEAP L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st' LB n lo m m_pre r RNG2 ms',
amalloc_post CI AHEAP L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st' LB n lo m_pre r RNG2 ms' ->
fp_le RNG RNG1 -> aheap_pres CI LB (bv_unsigned sp) m m_pre ->
amalloc_post CI AHEAP L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m r RNG2 ms'.
Proof.
intros until ms'. intros PM LE PRES. unfold amalloc_post in *.
destruct PM as (FP & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & E & MI & ST & PR & REST).
split; [eapply fp_le_trans; [exact LE | exact FP]|].
exists t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, t3, t4, t5, t6, m'. split; [exact E|]. split; [exact MI|]. split; [exact ST|].
split; [eapply aheap_pres_trans; [exact PRES | exact PR] | exact REST].
Qed.
#[using="Type"] Lemma ablocks_xbusyG : forall L st st' X X' LB, ablocks L st X LB -> x_busy X' = x_busy X -> a_live st' = a_live st -> ablocks L st' X' LB.
Proof. intros. eapply ablocks_same; eassumption. Qed.
Section Pres.
Variables (sp t SB c mu ACL lo : Z).
Notation Wp := ([(sp - 4096, sp); (t + 208, t + 3169); (AINSTANCE, AINSTANCE + 728); (SB + 137438953472 + c * 128, SB + 137438953472 + c * 128 + 128);
(SB + c * 4294967296 + mu, SB + c * 4294967296 + 4294967296);
(shad (SB + c * 4294967296 + mu), shad (SB + c * 4294967296) + 536870912)]%Z) (only parsing).
Definition pfactsG : Prop :=
(ACL = ATOP /\ ACL <= lo /\ lo <= sp - 4096 /\ sp <= 2^47)
/\ (4096 <= t /\ t + 4096 <= ACL /\ (t + 4096 <= 2147446784 \/ 17594333495296 <= t) /\ (t + 4096 <= 65536 \/ 6254592 <= t))
/\ (17594333495296 <= SB /\ SB + 137438957568 <= ACL /\ SB mod 65536 = 0 /\ 1 <= c <= 31 /\ 0 <= mu <= 3758096384 /\ mu mod 8 = 0)
/\ (t + 4096 <= SB \/ SB + 137438957568 <= t).
Hypothesis PF : pfactsG.
#[using="rc ACL lo PF"] Lemma Q_stack : forall A k, sp <= A -> 0 <= k -> disjoint_from Wp A k.
Proof. intros. pose proof PF as (F1 & F2 & F3 & F4). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0060>19724415300.3224466276229.4627033913167.3244609426123.3257242100943.3264226637918.3200000@00Z00d00g010019S1H2F12F22F33H11S1H2F12F22F32H62H73H113H21S1H2F13H11S1HS1H2F12F3S1H2F12F3".
repeat split; try exact I; Z.div_mod_to_equations; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc ACL lo PF"] Lemma Q_img : forall A k, 0x10000 <= A -> 0 <= k -> A + k <= 6254592 -> (A + k <= AINSTANCE \/ AINSTANCE + 728 <= A) -> disjoint_from Wp A k.
Proof. intros. pose proof PF as (F1 & F2 & F3 & F4). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0060>19724415298.3424466276227.4827033913161.3444609426125.3457242100937.3464226637912.3400000B00]00a00l01301:S1H2H12H22F22F32H3S2H12F22F32F42H32H43H133H18S2H2S2H12F13H13S2H12F3S2H12F3".
repeat split; try exact I; Z.div_mod_to_equations; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc ACL lo PF"] Lemma Q_slot : forall A k, SB <= A -> 0 <= k -> A + k <= SB + 137438953472 ->
(A + k <= SB + c * 4294967296 + mu \/ SB + c * 4294967296 + 4294967296 <= A) -> disjoint_from Wp A k.
Proof. intros. pose proof PF as (F1 & F2 & F3 & F4). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0060>19724415298.3424466276227.4827033913161.3444609426125.3457242100937.3464226637912.3400000B00h00n01801<01CS1H2H12F22F32F42H3S1H2H12H22F22F32F42H32H42H82H93H133H18S1H2F3S2H12F12F3S2H2S2H12F3".
repeat split; try exact I; Z.div_mod_to_equations; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc lo PF"] Lemma Q_obj : forall A k, ((6254592 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> 0 <= k -> A + k <= ACL -> (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) -> disjoint_from Wp A k.
Proof. intros. pose proof PF as (F1 & F2 & F3 & F4). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0060>19724415299.3524466276226.4927033913160.3544609426124.3557242100936.3564226637913.3500000400e00h00o01G01_S2H2S1H2H02H22H32F12F22F32F42H42H52H93H103H143H193H24S1HS2H12F1S1H2H02H22H32F22F32F42H4S1H2H02H22H32F22F32F42H4".
repeat split; try exact I; Z.div_mod_to_equations; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc lo PF"] Lemma Q_shad_hi : forall a, ACL <= a < 2^47 -> disjoint_from Wp (shad a) 1.
Proof. intros. pose proof PF as (F1 & F2 & F3 & F4). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0060>10572078974.3711350039626.3735787683850.3741594229125.5162254393123.378497269205.37 00000@00P00e01@01\025S1H2F12H02H13H15S1H2F12H02H13H15S1H2F22F32F42H02H12H5S1H2F22F32H02H13H103H113H15S1H2F12F22F32F42H02H12H53H15S1H2F12F22F32H02H12H53H15".
repeat split; try exact I; Z.div_mod_to_equations; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc ACL lo PF"] Lemma Q_shad_img : forall a, 0x10000 <= a < 6254592 -> disjoint_from Wp (shad a) 1.
Proof. intros. pose proof PF as (F1 & F2 & F3 & F4). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0060>10572078974.3711350039626.3735787683850.3741594229125.5162254393123.378497269205.37 00000@00I00^01>01S01eS1H2F12H02H13H15S1H2H02H1S1H2F22F32F42H02H12H5S1H2F22F32F42H02H12H52H63H153H20S1H2F22F32F42H02H12H5S1H2F22F32H02H12H5".
repeat split; try exact I; Z.div_mod_to_equations; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
#[using="rc lo PF"] Lemma Q_shad_obj : forall a, ((6254592 <= a /\ a + 1 <= 2147446784) \/ 17594333495296 <= a) -> a < ACL -> (a + 1 <= SB \/ SB + 137438957568 <= a) -> disjoint_from Wp (shad a) 1.
Proof. intros. pose proof PF as (F1 & F2 & F3 & F4). unfold AINSTANCE in *. cbn [disjoint_from]. rewrite !shad_div. unfold ASHOFF. Local Ltac2 Set LiaHints.tbl := fun () => "0060>10572078960.3911350039620.3935787683844.3941594229131.5362254393133.398497269211.39 00000G00Y01;01f02H02jS2H02F12F22F32H22H33H17S1H2H12F22F42H22H3S1H2H02H12F12F22F32F42H22H32H73H17S1H2H12F22F32F42H22H32H72H83H123H133H173H22S1H2H02H12F12F22F32F42H22H32H73H17S1H2H02H12F12F22F32F42H22H32H73H17".
repeat split; try exact I; Z.div_mod_to_equations; lia. Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End Pres.
Section S.
Variable DI : ADepotIface.
Variables (AQ ASEC : alayout -> astate -> aconc -> amem -> Prop) (AFK : alayout -> list ablock -> amem -> Prop).
Hypothesis HL : ahole_laws (AH DI AQ ASEC AFK).
Variable CI : list (Z * Z).
Hypothesis CI_OK : Forall (fun iv => 0x10000 <= fst iv /\ (snd iv <= ADEPOT_LO \/ ADEPOT_HI <= fst iv) /\ snd iv <= AIMG_HI) CI.
Hypothesis CI_OK2 : Forall (fun iv => snd iv <= AINSTANCE \/ AINSTANCE + 728 <= fst iv) CI.
#[using="HL CI_OK CI_OK2"] Theorem amalloc_prim : forall (L : alayout) (RNG : footprint)
(ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
(F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (LB : list ablock) (n lo : Z) (tr : list Z) (RESV : list (Z * Z)),
is_primary n = true ->
AHEAP_P (AH DI AQ ASEC AFK) L RNG st LB m ->
mem_inv asegs m ->
stk asegs m lo (bv_unsigned sp) -> ATOP + 4096 <= lo -> lo <= bv_unsigned sp - AMALLOC_STACK ->
tp = Z_to_bv 64 ATP ->
a0 = Z_to_bv 64 n -> 1 <= n <= AREQMAX ->
aunw m L RNG lo AMALLOC_PC sp s0 ra tr ->
bv_unsigned s0 <> bv_unsigned sp + 8 -> 4096 <= bv_unsigned ra -> bv_unsigned ra <> AMALLOC_PC ->
bv_unsigned sp mod 16 = 0 ->
rng RNG lo (bv_unsigned sp - lo) ->
aresv_ok L RESV ->
implS asegs RNG (aembed ATOP (amalloc ATOP RESV st n))
(epostF (amalloc_post CI (AHEAP_P (AH DI AQ ASEC AFK)) L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st LB n lo m))
(MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
F (Z_to_bv 64 AMALLOC_SYM) fc None m (seg_rom asegs)).
Proof.
intros until RESV. intros PRIM AHP MI ST BOT LO TP Ha0 NR AUNW S0NE RA4 RANE SP16 RSTK ROK.
assert (N : 1 <= n <= AREQMAX) by exact NR. Local Ltac2 Set LiaHints.tbl := fun () => "03:0?103190523.53   1043613157.30  1047820382.30  1047820382.74  1048973970.40  11753044101.1  12795064095.11 13834823456.22 14678803774.53 15113417066.6  15614790757.17 15614790757.18 15952863689.30 16087994273.2  16139936546.53 16235674075.69 16701876745.15 1708184202.8   17579378290.69 17794445592.74 17986879152.18 17986879152.30 17986879152.74 17986879152.8  17991058187.30 1831849320.9   18443648257.53 18458005471.14 18752057711.53 18876924192.8  19033156465.30 19043498592.22 20071147854.53 20247974688.22 20747552278.30 21198318311.69 21896864159.46822685041445.30 22985433830.53 23075035164.6  23146202366.53 23221066441.5  23750122331.53 2431149150.2   24815477526.5  24833872800.22 26290885301.61 26496924968.22 26496924968.23 26496924968.27 26496924968.30 26496924968.35 26496924968.36 26496924968.37 2752957518.18  28424009558.53 28573890679.10 28573890679.7  28782437782.53 28815543264.22 29462113485.33 29782367974.41229782367974.41829782367974.42029782367974.42129782367974.50129971683454.2  30058057083.53 30083344102.53 30547848657.53 30940542853.14 31246782368.22 32055749010.30 32064677718.53 32097467486.8  32157486868.11 32609415441.53 33593804012.4  33595851885.30 33681413138.13 33686640032.22 3448063264.22  34494795521.53 35592600517.74 35700282015.1  35713220113.10 3573724046.27  35981009970.53 362168202.11   36480049053.2  36624462341.24 36782690527.2  37444447563.53 38046792571.53 3826388185.6   39170548385.16 39188636933.0  39774293880.3  39807547359.53 39895290829.2  40651163129.7  41624889760.22 42470507449.61 42641743035.53 42697206566.53 43134119952.22 43195871047.53 44383525240.17 44503560193.74 44662057650.69 4515388254.3   45204448115.2  45614948832.22 46643532308.5  46643634869.6  46895961647.53 46987805029.1  47155058357.6  47233494002.11 47928819638.53 49127785425.53 49453249574.53 50018772662.53 5003033581.53  50850525385.0  51434861093.10 51794542621.6  51816399887.11 52041393011.74 52569147371.26 52620565557.3  53238998938.2  53383599078.11 53391091466.3335449560974.27  54686151809.17 54969794426.30 55097751038.15 55588686165.0  55923564877.92 56023370143.46856174447011.11 56972504806.53 57162972006.53 57207515515.53 57628698627.9  57818248480.22 5806317733.17  5806317733.18  58414835857.92 58422691744.22 58516855249.53 59029906444.17 59029906444.18 59363794864.1  59577709695.53 59693539158.53 59790178479.53 60190386007.0  60475348926.53 6083973208.13  60864384416.22 6107023078.53  61734812484.17 61789444896.22 62000065617.53 63374621462.46664637685054.53 64811016548.69 65149873711.53 65504523926.46466034437902.11 66056838816.22 66149329551.24 66149329551.27 66295356734.53 66383365888.22 66471504474.53 66992373344.22 6718031719.74  67289562894.53 67352811839.53 67469470029.43 6753474285.3   6753655066.11  6755542714.6   6758013062.17  6758013062.18  67643844143.53 67782583095.0  68148159701.13 7825503770.12  8075722198.53  8129703265.1   8806422860.10  8806422860.9   8934443006.30  9255215264.22  9289213154.10  9690010516.6   9690374965.6   9692079909.3   00000:00?00D00I00k00l01701V01[01a02=02]02c02g03h04I04d04m05N05V05[05`05e05j05o06906>06O06X06_06l07K07P07o08308N08l09209?09K09P09Y0:?0:B0:K0:j0;X0<70<L0=;0=R0>M0?L0@?0@]0@b0@o0A80A=0A\0B70BU0C30CQ0Co0DM0DQ0D[0D`0Da0E;0EZ0Ej0Eo0F70FK0FL0FS0FY0G20GQ0H00H10H:0H;0H@0Hk0Il0J60J;0JX0J\0Jf0K00K60KD0KE0KJ0LN0LO0Lc0MB0N<0NF0NO0Nn0O<0OV0O\0P10P70P<0P[0P_0Pc0Pl0Pm0Q30QD0QQ0QR0Q_0R40RF0RG0RP0RT0R_0Rd0S?0SD0SI0ST0Se0TV0U00U80UO0UP0VU0W30W90WF0WS0W]0Wa0X@0XN0X]0Ym0ZL0ZM0Zc0[=0[>0[C0[H0[Q0[R0[W0\00\O0\\0\k0]J0]K0]i0]n0_10_:0_X0_k0`J0`^0a20a70aV0ac0bB0bN0bW0b`0cY0cZ0c[0c\0c]0c^0cg0ch0d?0dP0dU0dV0d_0dh0dk0eJ0eU0eZ0e_0edS3BOT2LO1HS3SP2S3CL2S3CL2S2G33RZM1H2H02H42H52H93H103H143H19SS1R3Bb13FITS3BOT2LO3C165TIMGa5TIMGb4HspA1HS3PF3S1R2Q3S3ORS1R3Gs43Gs52Ct2SF3RSP2CrS4OFKi5D_t_f1R2K12K33RSP7D_f_resS4STK1S2L1S3C164OFKi3PF33PF43FKO3ORS3RSP7D_f_res5D_t_f7D_d_res5D_t_d3ODT2OTS2F32F52F62H93H103H143H153H243H29S4SHM14SHM23GR33GR43GR53GR7S3KS03KS1S4OFKi2F12F33FKO3RSP1H2H03H193H29S3SP12G1S3BOTS3BOTS3BOTS3BOTS3BOTS3RZR1H2H0S3SF1S3C163SP21H2H02H4S3SF43SF5S2M12M2S2LO3BOT4STK3S3BOT2LO3C165TIMGa5TIMGb4HspA1HS3PF3S3BOT2LO3C165TIMGa5TIMGb4HspA1HS2H2S2F23FKO3RSP1H2H02H42H53H34S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S1H2H0S5TIMGa5TIMGbS2NS3RSR3NSZS3PF3S3C163KS0S5OFKsa5OFKsb4SHHI3SF43SF55DBNDa5DBNDbS1NS1R2Q12Q3S3BOT2LO3C165TIMGa5TIMGb4HspA1HS3NSZ2NS3RSR4SM162M01H2H02H42H52H93H103H143H24S3BOT2LO3C165TIMGa5TIMGb4HspA1HS3BOT2LO3C163TL24HspAS3BOT2LO2NS3RZR3RSR3C163NSZ3SP24HspA2G23EUB3DJTS3BOT2LO3C163CL24HspA1YS3BOT2LO3C165TBNDa5TBNDb4HspA3GR23GR33GR43GR53GR63GR83GR91HS3BOT2LO3C165TBNDa5TBNDb4HspA3GR23GR33GR53GR63GR73GR83GR93SB31HS3BOT2LO3C165TBNDa5TBNDb4HspA3GR33GR73GR83SB33SB41HS2G42G53B1'3RZR3EUB3NSZ2NS3RSRS3PF3S3C164HspA2HqS4HspA2HqS3PF3S3BOT2LO3C165TIMGa5TIMGb4HspA1HS3SP33B4'1H2H02H42H52H93H14S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S2NRS3BOT2LO1HS3PF3SS2G42G53B1'3RZR3NSZ2NS3RSRS3BOT2LO3C165TIMGa5TIMGb4HspA1HS2H43SP11H2H02A4S3PF3S3BOT2LOS2G43B1'3B2'3C163SZBSS2T12K2S4SP47S3GR43GR63GR93GR33GR53SLSS3BOT2LO3C165TIMGa5TIMGb4HspA1HS3BOT2LO3C165TIMGa5TIMGb4HspA1HSS3GR33GR7SS3STaS3BOT2LO2NS3RZR3RSR3C163NSZ3SP24HspA2G23DJTS3C164OFKi3PF33PF43FKO3ORS3RSP7D_f_res5D_t_f7D_d_res5D_t_d3ODT2OTS3NSZ1H2H0S3C16S2G12G23SP13SP21H2H02H42H52H9S2QSS3BOT2LO1HS3BOT2LO1HS1R2Q1S1N1H2H02H42H5SS3DJCS3BOT2LO4OFKi3PF33PF43FKO3ORS3RSP7D_f_res5D_t_f7D_d_res5D_t_d3ODT2OTSS3POS4HCNT5CNTB'3MCBS3BOT2LO3C165TIMGa5TIMGb4HspA1HS3NSZ2NS3RSR3RSM4SM162M01H2H02H42H52H93H103H143H153H243H29S3BOT2LO1HS3PF33SF2S3BOT2LO3C165TIMGa5TIMGb4HspA1HS3BOT2LO3SF21HS4OFKi5OFKsa5OFKsb1R2K12K3S4LTRCS2F12F32F42H93H103H29S4HspAS3NSRS3BOT2LO3C165TIMGa5TIMGb4HspA1HS2KRS2Q1S3SF43SF5SS1R2Q4S3C163B1'3B2'3KS1S5TIMGa5TIMGbSS5TIMGa5TIMGbS5TBNDa5TBNDb3SF13SF2S4OFKi5DIMGa5DIMGbSS2LO4HspAS2KRS1R3Bb23FITS3NSZS3BOT2LO3C163SP23TL24SHHI1HS3STaS3Gs5S1R3Bb33FITS4LTRC3LSJ3LTB2L2S3BOT2LO1N2NS3RZR3RSR3C163NSZ3SP24HspA2G23EUB3DJTS4OFKi3RSP7D_f_res1R2K12K3S4STK31HS4SHM14SHM23GR33GR53GR7SS2G42G53B1'1N3NSZ3RSR2NS2G34REG81e1H2H42H52H93H103H143H153H193H243H29S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S4HspAS5TIMGa5TIMGbS5TIMGa5TIMGbS3BOT2LO1HS2HqS3BOT2LO3C165TIMGa5TIMGb4HspA1HS1R3Gs33Gs42SFS4OFKi3FKO1R2K3S2G42G53B1'3NSZ3RSR3RSM2NS2G34REG82n01H2H42H52H93H103H143H153H193H243H253H293H44S3BOT2LO3C165TIMGa5TIMGb4HspA1HSS3ORS1R3Gs23Gs43Gs52SFS4OFKi5OFKsa5OFKsb1R2K12K3SS3SF3S3PF3S3SF43SF5SS3PF3S2A12Q12Q22P52P42R12R22R3S3BOT2LO3C165TIMGa5TIMGb4HspA1HS5TIMGa5TIMGbS4OFKi3FKO1R2K3S3BOT2LO3C165TIMGa5TIMGb4HspA1HSS4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S3PF3S2F32F42F52F63FKO3RSP7D_f_res1H2H02H42H52H93H103H143H153H193H243H29S3SF43SF5S4LTRC3LSJ3LTB2L24LSJ'3LCH3KS0S3BOT2LO3SPR4HspA1HS3BOT2LO3C165TIMGa5TIMGb4HspA1HS3RZM3RSM1H2H02H42H9S3SP33KS21H2H02H42H9S3PF3S3BOT2LO3C165TIMGa5TIMGb4HspA1HS5D_t_f5D_t_dS3BOT2LO3C165TIMGa5TIMGb4HspA1HS3SP22G23EUBS3PF33SF2S3SF43SF5S3BOT2LO3DL23DL54HspA2Hq1H3C165TIMGa5TIMGb4NODi4STOi1Y2Y0SSSSSS3SF43SF5SS4SHM14SHM23GR33GR43GR7S3C162Q12Q22P52P4S3PF3SS4HspA2HqS4HspA2HqS1YS3BOT2LO3C165TIMGa5TIMGb4HspA1HS3RZR3RZM1HS3SZBS3SZBS3SZB".
assert (N1 : 1 <= n) by (clear -NR; lia).
assert (EXARM : exists trc,
((bv_unsigned sp + 16 < al_top L /\ uchain m (al_top L) AMALLOC_PC (bv_unsigned sp) (bv_unsigned s0) 28%nat tr /\ (length tr <= 28)%nat /\ trc = bv_unsigned ra :: tr
/\ rng RNG lo (al_top L - lo))
\/ (al_top L <= bv_unsigned sp + 16 /\ bv_unsigned sp < 2^47 /\ trc = []))
/\ In (AMALLOC_PC :: trc) (al_U L) /\ (length trc <= 29)%nat /\ bv_unsigned sp < 2^47).
{ pose proof (alayout_stack L (proj1 AHP)) as (K1 & K2 & K3).
destruct AUNW as [(T1 & U1 & L1 & I1 & R1)|(T1 & T2 & I1)].
- exists (bv_unsigned ra :: tr). split; [left; split; [exact T1|]; split; [exact U1|]; split; [exact L1|]; split; [reflexivity| exact R1]|].
split; [exact I1|]. split; [cbn [length]; clear -L1; lia | clear -T1 K2; lia].
- exists (@nil Z). split; [right; split; [exact T1|]; split; [exact T2| reflexivity]|]. split; [exact I1|]. split; [cbn [length]; clear; lia | exact T2]. }
destruct EXARM as (trc & ARM & TRU & LTRC & SP47).
destruct AHP as (ALO & ARNG & [X [AR BL]] & HFK).
remember (class_id (needed_size n)) as c eqn:HC0. symmetry in HC0.
pose proof (prim_facts n N1 PRIM) as (NS & RZR & RZE & RZM & RLR & RSR & RSM & NSR).
pose proof (prim_class_facts n c N1 PRIM HC0) as (C16 & NSZ & SM16 & SMALL & MCB). clear SMALL.
pose proof (cls_facts c C16) as (SZB & _ & _ & _).
assert (HCK : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -C16; lia).
assert (NM8 : needed_size n mod 8 = 0) by (rewrite NS; clear -RSM RZM; Z.div_mod_to_equations; lia).
pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
destruct THR as (T0 & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
destruct (PERC c HCK) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
pose proof (alayout_depot L ALO) as (DL1 & DL2 & DL3 & DL4 & DL5 & DL6 & DL7 & DL8 & DL9 & DL10).
pose proof (aobj4_int _ (ao_t L ALO)) as (_ & _ & (kT & TBND & TBNDa & TBNDb) & (jT & TIMG & TIMGa & TIMGb)).
pose proof (aobj_int _ _ (ao_ctx L ALO) ltac:(clear; lia)) as (CTXi & _ & (kC & CBND & CBNDa & CBNDb)).
pose proof (aobj_int _ _ (ao_nodes L ALO) ltac:(clear; lia)) as (NODi & _ & (kN & NBND & NBNDa & NBNDb)).
pose proof (aobj_int _ _ (ao_store L ALO) ltac:(clear; lia)) as (STOi & _ & (kR & SBND & SBNDa & SBNDb)).
pose proof (aobj_int _ _ (ao_fake L ALO) ltac:(clear; lia)) as (OFKi & _ & (kF & OFKs & OFKsa & OFKsb)).
pose proof (aobj4_int _ (ao_dtls L ALO)) as (_ & _ & (kD & DBND & DBNDa & DBNDb) & (jD & DIMG & DIMGa & DIMGb)).
pose proof (alayout_stack L ALO) as (STK1 & STK2 & STK3).
pose proof (alayout_res_disj L ALO) as [SCX TSP].
pose proof RT as RT0.
destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
& PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
pose proof INI2 as INI. rw_split INI 1%nat INI1 INIx. clear INIx.
pose proof OOM3 as OOM. rw_split OOM 2%nat OOMx RSS. clear OOMx.
pose proof IMAX4 as IMAX. rw_split IMAX 3%nat IMAX3 IMAXx. clear IMAXx.
pose proof T0 as TT0. rw_split TT0 1%nat TTctx TT.
pose proof ARNG as ARNG0. destruct ARNG as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS).
assert (RCTX4 : rng RNG (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX|]; clear; lia).
word_range sp SPR.
box CL5. box DL7. box DL8. box DL9. box DL10. box TSP. box SCX.
rewrite (amalloc_prim_eq RESV st n c N1 PRIM HC0).
iprefix. eapply evtF_cut.
{ eapply (malloc_pre_spec L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m n (al_t L) lo (al_top L) (al_bot L) tr trc).
all: try lazymatch goal with
| |- stk _ _ _ _ => exact ST
| |- mem_inv _ _ => exact MI
| |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- u64arr _ _ _ _ => exact STATS
| |- (_ /\ _) \/ (_ /\ _) => exact ARM
| |- _ \/ _ => unboxed CL5
| |- @eq word _ _ => first [exact TP | exact Ha0]
| |- is_primary _ = _ => exact PRIM
end.
all: try lazymatch goal with
| |- rw_cells _ _ _ _ => assumption
| |- rng _ _ _ => assumption
end.
all: try assumption.
all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 LTRC RA4 SP16;
clear; intros; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH in *; lia).
all: match goal with |- ?G => idtac "REMPRE" G end. }
cbv beta. intros ms4 P4. unfold malloc_pre_post in P4.
destruct P4 as (spA & t0c & t1c & t2c & a4c & a5c & a6c & a7c & t3c & t4c & t5c & t6c & s0A & s1A & s2A & s3A & s4A & s5A & s0i & fr0 & junk2 & tb & m4
& -> & HspA & MU4 & WM4 & MI4 & ST4 & FRa & FR16 & SS & TB & LTB & TRF & FRS & UW4).
apply evtF_done.
assert (AR4 : AREP (AH DI AQ ASEC AFK) L st X m4).
{ eapply (AREP_frame_pre _ HL L st X m m4); [exact ALO | exact AR | exact MU4 | exact WM4 | | exact UW4].
apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; left; unfold AMALLOC_STACK in *; clear -LO BOT STK3; lia|].
apply Forall_cons; [unfold apre; cbn [fst snd]; intros _; right; split; reflexivity| apply Forall_nil]. }
eapply (@calloc_arep_gen _ _ HL _ _ _ L RNG _ _ gp tp t0c t1c t2c _ _ _ _ _ _ a4c a5c a6c a7c _ _ _ _ _ _ _ _ _ _ t3c t4c t5c t6c F fc m4 st X c lo (needed_size n)
ALO ARNG0 AR4 MI4).
all: try lazymatch goal with
| |- arng _ _ _ => exact ARNG0
| |- stk _ _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) by (clear -HspA; lia); exact ST4
| |- ATOP <= _ => clear -LO BOT STK3; unfold AMALLOC_STACK in *; lia
| |- _ <= bv_unsigned _ - _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
clear -LO HspA BOT STK3; unfold AMALLOC_STACK in *; lia
| |- @eq word _ _ => first [exact TP | reflexivity]
| |- 16 <= _ <= 65536 => clear -NSR; lia
| |- _ mod 8 = 0 => exact NM8
| |- class_id _ = _ => exact HC0
| |- rng _ _ _ => rewrite unsigned_lit by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia);
eapply rng_sub'; [exact RSTK|]; clear -LO HspA SP47 BOT STK3; unfold AMALLOC_STACK in *; lia
end.
intros st_pre X_pre RNG1 m_pre cnt k ms1 CRET. unfold calloc_retG in CRET.
destruct CRET as (FPLE & ARp & ARNGp & HCNT & POS & NK & NB & KR & XB & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & MUc & WMc & MIp
& t0d & t1d & t2d & a1d & a2d & a3d & a4d & a5d & a6d & a7d & t3d & t4d & t5d & t6d & m1 & stj1 & -> & MU1 & WM1 & MI1 & ST1 & CR1 & STS1).
rewrite ?unsigned_lit in MUc by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
rewrite ?unsigned_lit in MU1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
rewrite ?unsigned_lit in ST1 by (clear -SPR HspA LO BOT STK3; unfold AMALLOC_STACK in *; lia).
replace (bv_unsigned spA + -128) with (bv_unsigned sp - 2272) in ST1 by (clear -HspA; lia).
cbn beta iota. apply implS_ret.
replace (ret_pc (Z_to_bv 64 0x3273c)) with (Z_to_bv 64 0x3273c) by (symmetry; apply ret_pc_even; [lia|reflexivity]).
pose proof ARp as AR0. destruct AR0 as (WF' & RT' & INST' & THR' & CLS' & HQ' & HS' & HD' & HRO' & RT2' & AVL' & RT3').
destruct THR' as (T0' & T40' & CACHES' & CSTATS' & [sj' [STATS' LSJ']] & UNW').
pose proof WF' as WF0. destruct WF0 as (SBE' & PAE' & SAL' & SLO' & SHI' & PERC' & OUTC' & BUSY' & LIVE' & FRESH' & UNIQ').
destruct (PERC' c HCK) as (B1' & B2' & B3' & B4' & B5' & B6' & B7' & LENF' & LENC' & CNTB' & ND' & RANGE').
destruct (kit_cache_pop _ L st_pre X_pre m_pre c cnt ARp HCK HCNT POS) as (k' & chunks & NK' & _ & _ & CR & CH & LCH & NTH & JK & FSH).
assert (EK : k' = k) by (rewrite NK in NK'; injection NK'; intros E; symmetry; exact E). subst k'.
set (S := size_of_class c) in *.
set (AB := aslot_addr L c k) in *.
assert (KSF : 0 <= k * S /\ k * S + S <= c_allocated_user (get_cls st_pre c) /\ (k * S) mod 16 = 0).
{ unfold ndist in KR. fold S in KR. fold S in SZB. fold S in SM16.
assert (P0 : 0 <= k * S) by (clear -KR SZB; apply Z.mul_nonneg_nonneg; lia).
assert (Q1 : k + 1 <= c_allocated_user (get_cls st_pre c) / S) by (clear -KR; lia).
assert (M1 : (k + 1) * S <= c_allocated_user (get_cls st_pre c) / S * S) by (apply Z.mul_le_mono_nonneg_r; clear -Q1 SZB; lia).
pose proof (Z.mul_div_le (c_allocated_user (get_cls st_pre c)) S ltac:(clear -SZB; lia)) as M2.
split; [exact P0|]. split.
- rewrite Z.mul_add_distr_r, Z.mul_1_l in M1. rewrite (Z.mul_comm S) in M2. clear -M1 M2 P0 SZB. lia.
- destruct (proj1 (Z.mod_divide S 16 ltac:(clear; lia)) SM16) as [q Hq]. rewrite Hq.
replace (k * (q * 16)) with ((k * q) * 16) by (clear; lia). apply Z_mod_mult. }
destruct KSF as (KS0 & KS1 & KS2).
assert (GEO : al_space_beg L <= AB /\ AB + S <= al_space_beg L + K_SPACE_SIZE /\ AB mod 16 = 0
/\ AB + S <= aregion L c + c_allocated_user (get_cls st_pre c) /\ aregion L c <= AB).
{ subst AB. unfold aslot_addr, aregion, K_REGION, K_SPACE_SIZE, K_FREEARR_OFF, K_ALIGN in *. fold S.
remember (k * S) as KS eqn:HKS. clear HKS.
change (2^37) with 137438953472. change (2^32) with 4294967296 in *.
split; [clear -KS0 C16; lia|]. split; [clear -KS1 B1' B2' C16 NSZ; lia|]. split; [| clear -KS0 KS1 B1'; lia].
clear -SP3 C16 KS2. Z.div_mod_to_equations; lia. }
destruct GEO as (G1 & G2 & G3 & G4 & G5). unfold K_SPACE_SIZE in G2. change (2^37) with 137438953472 in G2.
assert (EAB : AB = aslot_addr L c k) by reflexivity. clearbody AB.
assert (ES : S = size_of_class c) by reflexivity.
assert (RZC : rz_size n = 16 \/ 32 <= rz_size n) by (clear -RZR RZM; Z.div_mod_to_equations; lia).
destruct (slot_carveG m_pre AB S n (rz_size n) JK RZC ltac:(clear -N; lia) ltac:(fold S in NSZ; clear -NSZ NS RSR; lia))
as (b0 & b1 & szh & szl & ctxj & uj & j1 & j2 & HDR & B1 & UJ & LH & TL).
set (UB := AB + rz_size n) in *. assert (EUB : UB = AB + rz_size n) by reflexivity. clearbody UB.
set (grz := shlen (rz_size n)). set (g := shlen (n - n mod 8)). set (room := if n mod 8 =? 0 then 0 else 1).
assert (GR12 : grz = rz_size n / 8 /\ g = (n - n mod 8) / 8).
{ subst grz g. unfold shlen. rewrite !Z.shiftr_div_pow2 by lia. split; reflexivity. }
destruct GR12 as [GR1 GR2].
assert (GR3 : 2 <= grz) by (rewrite GR1; generalize RZR; clear; intros; Z.div_mod_to_equations; lia).
assert (GR4 : 0 <= g) by (rewrite GR2; generalize N; clear; intros; Z.div_mod_to_equations; lia).
assert (GR5 : 0 <= room <= 1) by (subst room; clear; destruct (n mod 8 =? 0); lia).
assert (GR6 : grz + g + room <= shlen S).
{ rewrite GR1, GR2. subst room. unfold shlen. rewrite Z.shiftr_div_pow2 by lia. change (2^3) with 8.
fold S in NSZ. fold S in SM16. generalize NSZ NS RSR RSM SM16 RZM RZR N. clear. intros.
destruct (Z.eqb_spec (n mod 8) 0) as [M0|M0]; Z.div_mod_to_equations; lia. }
assert (GR7 : shad UB = shad AB + grz).
{ rewrite GR1, EUB. unfold shad, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
generalize G3 RZM RZR. clear. intros. Z.div_mod_to_equations. lia. }
assert (GR89 : 0x2008fff7000 <= shad AB /\ shad AB + shlen S <= 0x10007fef8000).
{ unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. generalize G1 G2 SP1 SP2. clear. intros. Z.div_mod_to_equations. lia. }
destruct GR89 as [GR8 GR9].
destruct (shadow_carve m_pre (shad AB) (shlen S) grz g room FSH GR3 GR4 GR6 GR5) as (SHA & SHpre & [sjunk SHU] & SHP & SHsuf).
rewrite <- GR7 in SHU, SHP, SHsuf.
set (PG := shad UB + g) in *.
pose proof RT' as RT0.
destruct RT0 as (GPG' & GOT' & GOT80' & RIC' & LS1' & REAL' & IMAX4' & FLG5' & FLG' & HPP' & SHB' & CANP' & TI' & TK' & INI2' & LAY' & MCS' & OOM3'
& PGC' & HK2' & CF8' & CF34' & CSMT' & T88' & TSD' & LS2' & CT8' & CT').
pose proof INI2' as INI'. rw_split INI' 1%nat INI1' INIx. clear INIx.
pose proof OOM3' as OOM'. rw_split OOM' 2%nat OOMx RSS'. clear OOMx.
pose proof IMAX4' as IMAX'. rw_split IMAX' 3%nat IMAX3' IMAXx. clear IMAXx.
pose proof HK2' as HK'. rw_split HK' 1%nat HK1' HKx. clear HKx.
pose proof T0' as TT0'. rw_split TT0' 1%nat TTctx' TT'.
destruct (junk_split m_pre (al_t L + 2768) 16 16 CSTATS' ltac:(lia) ltac:(lia)) as [CSa CSb].
destruct (junk_split m_pre (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 CSc].
replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia.
replace (al_t L + 2768 + 16 + 8) with (al_t L + 2792) in CSc by lia.
destruct INST' as (I32' & I48' & I64' & I72' & I112' & I680' & I984' & I40' & I56').
pose proof ARNGp as ARNGp0. destruct ARNGp as (RIMG' & RT4' & RCTX' & RNO' & RST' & RRI' & RFK' & RSFK' & RDTLS' & RCLS' & RPA' & RSECS' & RPSH').
destruct (RCLS' c HCK) as (RREG & RSREG & RFA & RSFA).
destruct (alayout_slot_disj L AB 65536 ALO G1 ltac:(unfold K_SPACE_SIZE, K_FREEARR_OFF, aregion, K_REGION in *; generalize G4 B1' B2' C16 SP1 SZB; clear; intros; change (2^37) with 137438953472; lia) ltac:(clear; lia))
as (DJT & DJC & DJN & DJS & DJF).
assert (RUf : rng RNG1 (UB - 16) (n + 16)) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N EUB KS0 NSZ NS RSR; clear; intros; lia).
assert (RABf : rng RNG1 AB 16) by (eapply rng_sub'; [exact RREG|]; generalize G4 G5 B1' RZR N NSZ NS RSR; clear; intros; lia).
assert (REG8 : aregion L c mod 8 = 0 /\ c_mapped_user (get_cls st_pre c) mod 8 = 0).
{ unfold aregion, K_REGION, K_USER_MAP, K_ALIGN in *. generalize SP3 B4'; clear; intros. Z.div_mod_to_equations; lia. }
assert (SHM : shad (aregion L c) <= shad AB /\ shad UB + g + room <= shad (aregion L c) + shlen (c_mapped_user (get_cls st_pre c))).
{ rewrite GR7, GR2, GR1. unfold shad, shlen, ASHOFF. rewrite !Z.shiftr_div_pow2 by lia. change (2^3) with 8.
fold S in NSZ. fold S in SM16. subst room. generalize G4 G5 B1' N NSZ RSR RSM NS RZR RZM SM16 G3 EUB REG8; clear; intros.
destruct (Z.eqb_spec (n mod 8) 0); Z.div_mod_to_equations; lia. }
destruct SHM as [SHM1 SHM2].
assert (RSAf : rng RNG1 (shad AB) 1) by (eapply rng_sub'; [exact RSREG|]; generalize SHM1 SHM2 GR3 GR4 GR5 GR7; clear; intros; lia).
assert (RSUf : rng RNG1 (shad UB) (shlen (n - n mod 8))).
{ eapply rng_sub'; [exact RSREG|]. fold g. generalize SHM1 SHM2 GR3 GR4 GR5 GR7. clear. intros. lia. }
assert (RSPf : n mod 8 <> 0 -> rng RNG1 PG 1).
{ intros NE. eapply rng_sub'; [exact RSREG|]. subst PG.
assert (R1 : room = 1) by (subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity]).
rewrite R1 in SHM2. generalize SHM1 SHM2 GR3 GR4 GR7; clear; intros. lia. }
assert (SLS : shlen S <= 8192) by (fold S in NSZ; unfold shlen; rewrite Z.shiftr_div_pow2 by (clear; lia); change (2^3) with 8; clear -NSZ; Z.div_mod_to_equations; lia).
assert (SB34 : 0 <= shlen (n - n mod 8) <= 8192 /\ PG + 1 <= 0x10007fff8000).
{ subst PG. fold g. rewrite GR7. generalize GR4 GR6 GR9 GR3 GR5 SLS; clear; intros; lia. }
destruct SB34 as [SB3 SB4].
assert (RCTX4' : rng RNG1 (al_ctx L) 4096) by (eapply rng_sub'; [exact RCTX'|]; clear; lia).
assert (DJC4 : al_ctx L + 4096 <= AB \/ AB + 65536 <= al_ctx L) by (generalize DJC; clear; intros; lia).
assert (CNT16 : 0 < cnt <= 16).
{ unfold max_count in CNTB'. generalize POS HCNT CNTB' MCB; clear. destruct (a_cinit st_pre); intros; lia. }
assert (PGE : PG = shad UB + shlen (n - n mod 8)) by reflexivity.
assert (RSTK1 : rng RNG1 lo (bv_unsigned sp - lo)) by (eapply rng_fp_le; [exact FPLE | exact RSTK]).
set (mu0 := c_mapped_user (get_cls st c)) in *.
assert (OBJ : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
/\ shad (al_space_beg L + c * 4294967296) + 536870912 <= 17594333495296).
{ unfold aregion_info, aregion, K_REGION, K_SPACE_SIZE, ARI_STRIDE. change (2^37) with 137438953472. change (2^32) with 4294967296.
split; [reflexivity|]. split; [reflexivity|]. rewrite shad_div. clear -SP1 SP2 C16. unfold ASHOFF, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
Z.div_mod_to_equations. lia. }
destruct OBJ as (RIE & RBE & SHHI).
assert (MU41 : munch [(bv_unsigned sp - 3856, bv_unsigned sp - 2272); (al_t L + 208, al_t L + 3168); (AINSTANCE, AINSTANCE + 728);
(al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
(al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
(shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m4 m1).
{ eapply munch_trans; [eapply munch_weaken; [| exact MUc] | eapply munch_weaken; [| exact MU1]];
unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION, acache_addr in *; change (2^32) with 4294967296 in *;
rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA C16; lia. }
assert (WM41 : wmono asegs m4 m1) by (eapply wmono_trans; [exact WMc | exact WM1]).
unfold K_SPACE_SIZE, K_SPACE_EXTRA in SP2. change (2^37) with 137438953472 in SP2.
xport FRa MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
xport FR16 MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
xport SS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
xport TB MU41 WM41 ltac:(rewrite LTB; clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
xport FRS MU41 WM41 ltac:(clear -SPR LO BOT STK3 TL1 TL2 SP1 SP2 C16 SHHI TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold AMALLOC_STACK, AINSTANCE in *; lia).
xport HDR MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
xport UJ MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia).
xport SHA MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport SHU MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
assert (SHP1 : n mod 8 <> 0 -> rw_cells asegs m1 PG [C1 (Z_to_bv 8 250)]).
{ intros NE. specialize (SHP ltac:(subst room; generalize NE; clear; intros NE; destruct (Z.eqb_spec (n mod 8) 0); [exfalso; exact (NE ltac:(assumption)) | reflexivity])).
xport SHP MU1 WM1 ltac:(cbv delta [g grz room PG] in *; clear -HspA SPR GR1 GR2 GR3 GR4 GR5 GR6 GR7 GR8 GR9 SB3 SB4 LO BOT STK3 TL1 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia). exact SHP. }
assert (LH1 : 16 < rz_size n -> rw_cells asegs m1 AB [C8 j1; C8 j2]).
{ intros R16. pose proof (proj1 (LH R16)) as LH0.
xport LH0 MU1 WM1 ltac:(clear -HspA DJT SPR SP2 G1 G2 EUB RZR N NSZ NS RSR LO BOT STK3 C16; unfold acache_addr, AMALLOC_STACK, K_SPACE_SIZE in *; lia). exact LH0. }
xport GOT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport GOT80' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport REAL' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport SHB' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport CANP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport HPP' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport CSMT' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport FLG5' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport FLG' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport HK1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport LS1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport LS2' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport LAY' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport MCS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport CF34' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport INI1' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport RSS' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport IMAX3' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport TI' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport TK' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport T88' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATP88, AMALLOC_STACK in *; lia).
xport TSD' MU1 WM1 ltac:(clear -HspA SPR TL1 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ATSD, AMALLOC_STACK in *; lia).
xport CT' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
xport CT8' MU1 WM1 ltac:(ub CL5; clear -HspA Y SPR TL1 CL1 CL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb CTXi CBND CBNDa CBNDb; unfold acache_addr, AMALLOC_STACK, AIMG_HI in *; lia).
xport TTctx' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport UNW' MU1 WM1 ltac:(clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, AMALLOC_STACK in *; lia).
xport STATS' MU1 WM1 ltac:(rewrite LSJ'; clear -HspA SPR TL1 TL2 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb; unfold acache_addr, ASTATS_WORDS, AMALLOC_STACK in *; lia).
assert (DEP1 : ADEPOT DI L m1).
{ eapply (adi_frame DI); [exact HD' | exact MU1 | exact WM1 |]. unfold acache_addr.
repeat (apply Forall_cons; [cbn [fst snd]; intros q Hq; ub DL7; ub DL8; clear -Hq Y Y0 HspA SPR TL1 TL2 DL1 DL2 DL3 DL4 DL5 DL6 LO BOT STK3 C16 TBND TBNDa TBNDb TIMG TIMGa TIMGb NODi NBND NBNDa NBNDb STOi SBND SBNDa SBNDb; unfold AMALLOC_STACK, AIMG_HI in *; lia|]).
apply Forall_nil. }
assert (PF : pfactsG (bv_unsigned sp) (al_t L) (al_space_beg L) c mu0 ATOP lo).
{ unfold pfactsG. pose proof (ao_t L ALO) as OT. unfold aobj, sclr, iclr, KLS, AIMG_LO, AIMG_HI in OT.
unfold AMALLOC_STACK, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN, K_FREEARR_OFF, K_USER_MAP in *. change (2^37) with 137438953472 in *.
ub TSP. generalize LO BOT SP47 STK2 STK3 OT SP1 SP2 SAL C16 A1 A2 A4 Y. clear. intros.
repeat match goal with H : _ /\ _ |- _ => destruct H end.
repeat split; first [reflexivity | assumption | lia | Z.div_mod_to_equations; lia]. }
assert (MUall : munch [(bv_unsigned sp - 4096, bv_unsigned sp); (al_t L + 208, al_t L + 3169); (AINSTANCE, AINSTANCE + 728);
(al_space_beg L + 137438953472 + c * 128, al_space_beg L + 137438953472 + c * 128 + 128);
(al_space_beg L + c * 4294967296 + mu0, al_space_beg L + c * 4294967296 + 4294967296);
(shad (al_space_beg L + c * 4294967296 + mu0), shad (al_space_beg L + c * 4294967296) + 536870912)]%Z m m_pre).
{ eapply munch_trans; [eapply munch_weaken; [| exact MU4] | eapply munch_weaken; [| exact MUc]];
unfold sub_fp; cbn [outside]; intros q Hq; rewrite ?RIE, ?RBE in *; unfold K_REGION in *; change (2^32) with 4294967296 in *;
rewrite ?shlen_div in *; change (4294967296 / 8) with 536870912 in *; clear -Hq HspA; lia. }
assert (WMall : wmono asegs m m_pre) by (eapply wmono_trans; [exact WM4 | exact WMc]).
assert (BB : forall b, In b (x_busy X) ->
al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
/\ (xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + c * 4294967296 + mu0 \/ al_space_beg L + c * 4294967296 + 4294967296 <= xb_alloc L b)).
{ intros b Hb. destruct (BUSY b Hb) as [CLB _].
destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
{ apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
unfold xb_alloc. unfold K_NUM_CLASSES in CLB. unfold K_FREEARR_OFF in Q2.
destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
- rewrite EC in P5, P4, Q1, Q2 |- *. rewrite RBE in P5, P4. change (c_mapped_user (get_cls st c)) with mu0 in Q1, Q2.
clear -P5 P4 Q1 Q2 A1 A2 C16. unfold K_FREEARR_OFF in *. lia.
- pose proof (region_other_geo L c (xb_class b) ALO ltac:(clear -C16; lia) CLB NC) as (R1 & R2 & R3 & _). rewrite RBE in R2.
clear -P5 P4 Q1 Q2 R1 R2 R3 A1. lia. }
pose proof (ao_fake L ALO) as FKO. unfold aobj in FKO. pose proof (ao_res L ALO) as ORS. unfold aobj in ORS. pose proof (ao_space L ALO) as RSP.
pose proof (ad_fake_res L ALO) as D_f_res. pose proof (ad_t_fake L ALO) as D_t_f. pose proof (ad_dtls_res L ALO) as D_d_res. pose proof (ad_t_dtls L ALO) as D_t_d.
pose proof (ao_dtls L ALO) as ODT. unfold aobj in ODT. unfold adisj in D_f_res, D_t_f, D_d_res, D_t_d.
assert (FKD : forall cls FA sz, In (mkABlock (ABFake cls) FA sz) LB -> al_fake L <= FA /\ 0 <= sz /\ FA + sz <= al_fake L + 11571200)
by (intros cls FA sz Hin; exact (proj1 (proj2 BL) cls FA sz Hin)).
assert (PRES : aheap_pres CI LB (bv_unsigned sp) m m_pre).
{ intros a Ha CL. split; [| intros Hw; apply WMall; exact Hw].
apply MUall. rewrite wa_unsigned by exact Ha.
destruct CL as [STa | [CIa | [BLK | SH]]].
- eapply disjoint_outside; [eapply (Q_stack _ _ _ _ _ _ _ PF a 1); clear -STa; lia | clear; lia].
- destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3).
pose proof (proj1 (Forall_forall _ _) CI_OK2 iv Hiv) as Q4. cbn [fst snd] in *.
eapply disjoint_outside; [eapply (Q_img _ _ _ _ _ _ _ PF a 1); unfold AIMG_HI in *; clear -R Q1 Q3 Q4; lia | clear; lia].
- destruct BLK as (b & Hb & R). destruct b as [[p|cls] A n']; cbn [ab_addr ab_size] in R.
+ destruct (proj1 BL p A n' Hb) as [(xb & Hxb & Sb & Ub & Nb)|(mb0 & ms0 & Lp & EUA & Gs)].
* destruct (BB xb Hxb) as (Bb1 & Bb2 & Bb3).
pose proof (awf_fits L st X xb WF Hxb) as FIT. unfold xb_fits in FIT. rewrite Sb in FIT. unfold xb_user in Ub. subst A n'.
eapply disjoint_outside; [eapply (Q_slot _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Bb1 Bb2 Bb3 FIT; lia.
*
cbn [sec_wf1] in Gs. destruct Gs as (Gs1 & Gs2 & Gs3 & Gs4 & Gs5 & Gs6 & (Ct & Cc & Cr & Cp & Cn & Cs & Cf & Cd)).
pose proof (sec_facts n' ltac:(clear -Gs5; lia) Gs6) as SF. subst A. unfold SEC_UOFF, K_HIGH_MEM in *.
unfold ablk, KLS, AIMG_HI in Gs2.
eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia]; clear -R Gs2 Gs3 Gs4 Gs5 SF Ct Cr RSP ORS; lia.
+ destruct (FKD cls A n' Hb) as (K1 & K2 & K3). atop_facts.
eapply disjoint_outside; [eapply (Q_obj _ _ _ _ _ _ _ PF a 1) | clear; lia];
clear -R K1 K3 FKO D_t_f D_f_res RSP OFKi OFKs OFKsa OFKsb; lia.
- destruct SH as (a' & Ha' & ->).
destruct Ha' as [STa | [CIa | FK]].
+ eapply disjoint_outside; [eapply (Q_shad_hi _ _ _ _ _ _ _ PF a'); unfold AMALLOC_STACK in *; clear -STa LO BOT STK3; lia | clear; lia].
+ destruct CIa as (iv & Hiv & R). pose proof (proj1 (Forall_forall _ _) CI_OK iv Hiv) as (Q1 & Q2 & Q3). cbn [fst snd] in *.
eapply disjoint_outside; [eapply (Q_shad_img _ _ _ _ _ _ _ PF a'); unfold AIMG_HI in *; clear -R Q1 Q3; lia | clear; lia].
+ destruct FK as (cls & FA & sz & Hin & R). destruct (FKD cls FA sz Hin) as (K1 & K2 & K3). atop_facts.
eapply disjoint_outside; [eapply (Q_shad_obj _ _ _ _ _ _ _ PF a') | clear; lia]; clear -R K1 K3 FKO D_f_res RSP OFKi OFKs OFKsa OFKsb; lia. }
assert (HFKp : AFK L LB m_pre).
{ eapply (hf_frame _ HL L LB m m_pre); [exact HFK | exact MUall | exact WMall |].
unfold fake_untouched. pose proof (ao_t L ALO) as OT. unfold aobj in OT.
assert (SHF : 2148232704 <= shad (al_fake L) /\ shad (al_fake L) + shlen 11571200 <= 17594332446720
/\ (shad (al_space_beg L + c * 4294967296) + 536870912 <= shad (al_fake L)
\/ shad (al_fake L) + shlen 11571200 <= shad (al_space_beg L + c * 4294967296 + mu0))
/\ shad (al_space_beg L + c * 4294967296) <= shad (al_space_beg L + c * 4294967296 + mu0)
/\ 2201439137792 <= shad (al_space_beg L + c * 4294967296)).
{ rewrite !shad_div, !shlen_div. unfold ASHOFF in *. destruct PF as (_ & _ & (F1 & F2 & F3 & F4 & F5 & F6) & _).
clear -FKO F1 F2 F3 F4 F5 F6 D_f_res RSP OFKi OFKs OFKsa OFKsb. Z.div_mod_to_equations. dlia. }
destruct SHF as (SF1 & SF2 & SF3 & SF4 & SF5).
unfold AMALLOC_STACK, AINSTANCE in *. destruct PF as (PF1 & PF2 & PF3 & PF4).
repeat (apply Forall_cons; [cbn [fst snd];
clear -LO BOT STK3 SP47 STK2 OT FKO ORS RSP ODT D_f_res D_t_f D_d_res D_t_d C16 PF3 PF4 SF1 SF2 SF3 SF4 SF5 SHHI TL1 TBND TBNDa TBNDb TIMG TIMGa TIMGb OFKi OFKs OFKsa OFKsb DBND DBNDa DBNDb DIMG DIMGa DIMGb;
repeat (split; [lia|]); lia |]).
apply Forall_nil. }
eapply evtF_mono.
{ eapply (malloc_tail_gen DI L RNG1 ra sp gp tp spA t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d
s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s0A s1A s2A s3A s4A s5A s0i F fc m1
n (al_t L) c cnt AB UB PG room lo b0 b1 szh szl ctxj (1 + Z.of_nat (length trc))
(Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 S) stj1 j1 j2 (Z_to_bv 8 250) sj' sjunk uj fr0 junk2 tb trc).
all: try lazymatch goal with
| |- stk _ _ _ _ => exact ST1
| |- mem_inv _ _ => exact MI1
| |- allocA_cells _ _ _ => unfold allocA_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- poison_cells _ => unfold poison_cells; repeat (lazymatch goal with |- rw_cells _ _ _ _ => idtac | |- _ /\ _ => split end)
| |- ADEPOT _ _ _ => exact DEP1
| |- In _ _ => exact TRU
| |- u64arr _ _ (_ + 2800) _ => exact STATS'
| |- u64arr _ _ _ _ => exact TB
| |- map _ _ = _ => exact TRF
| |- (16 < _) -> _ => exact LH1
| |- ~ _ -> rng _ _ _ => exact RSPf
| |- ~ _ -> _ => exact SHP1
| |- is_primary _ = _ => exact PRIM
end.
all: try lazymatch goal with
| |- rw_cells _ _ (_ + -16) _ => exact HDR
| |- rw_cells _ _ (shad _) [C1 _] => exact SHA
| |- rw_cells _ _ (shad _) [CB _ _] => exact SHU
| |- rw_cells _ _ _ [CB _ _] => exact UJ
| |- rw_cells _ _ (_ + 2784) _ => exact STS1
| |- rw_cells _ _ (_ + 208 + _ * 80) _ => exact CR1
| |- rw_cells _ _ _ _ => assumption
| |- rng _ _ _ => assumption
| |- _ \/ _ => first [exact DJT | exact DJN | exact DJS | exact DJC4 | unboxed CL5 | unboxed DL7 | unboxed DL8 | unboxed DL9 | unboxed DL10]
| |- @eq Z _ _ => first [assumption | reflexivity | exact PGE | subst room; reflexivity]
| |- @eq word _ _ => first [assumption | reflexivity]
| |- @eq nat _ _ => first [exact LSJ' | exact LTB | assumption]
end.
all: try assumption.
all: try (generalize N NR LO BOT SP47 STK1 STK2 STK3 SP1 SP2 SP4 TL1 TL2 TL3 TL4 CL1 CL2 CL3 CL4 DL1 DL2 DL3 DL4 DL5 DL6
G1 G2 G3 G4 G5 EUB ES SM16 NSZ NS RSR RZR GR3 GR7 GR8 GR9 SB3 SB4 B1 POS HCNT CNT16 KS0 KS1 HC0 C16 LTRC RA4 HspA;
clear; intros; rewrite ?HC0 in *; unfold AIMG_HI, AMALLOC_STACK, AREQMAX, UDEPTH, K_SPACE_SIZE, K_SPACE_EXTRA in *; lia).
all: try (eapply rng_sub'; [exact RSTK1|]; clear -LO SP47 BOT STK3 SPR; unfold AMALLOC_STACK in *; lia).
all: try (clear -LTRC; lia).
all: match goal with |- ?G => idtac "REMT" G end. }
cbv beta. intros ms' PM.
unfold apop. rewrite HCNT, !a_next_put_cls, !a_live_put_cls.
apply (malloc_post_gen_shift DI L ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc n (al_t L) c cnt AB UB PG room lo b1 _ _ uj m_pre m1 ms') in PM;
[| eapply munch_weaken; [| exact MU1]; unfold sub_fp, acache_addr; cbn [outside]; intros q Hq; clear -Hq HspA; lia | exact WM1].
cbv delta [PG g grz room] in PM, SHpre, SHsuf. subst UB. subst AB.
eapply (amalloc_post_shiftG CI _ L RNG RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st st_pre LB n lo m m_pre); [| exact FPLE |].
{ eapply (store_prim DI AQ ASEC AFK HL CI CI_OK L RNG1 ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m_pre st_pre LB X_pre n lo c cnt k b1
(Z_to_bv 64 (max_count st_pre c)) (Z_to_bv 64 (size_of_class c)) uj).
all: try exact PM.
all: try lazymatch goal with
| |- is_primary _ = _ => exact PRIM
| |- alayout_ok _ => exact ALO
| |- arng _ _ _ => exact ARNGp0
| |- AFK _ _ _ => idtac
| |- AREP _ _ _ _ _ => exact ARp
| |- ablocks _ _ _ _ => eapply ablocks_xbusyG; [exact BL | exact XB | exact L1]
| |- nth_error _ _ = _ => exact NK
| |- busy_of _ _ _ = _ => exact NB
| |- (16 < _) -> _ => let R16 := fresh in intros R16; exact (proj2 (LH R16))
| |- junk_at _ (_ + 2768) _ => exact CSa
| |- junk_at _ (_ + 2792) _ => exact CSc
| |- junk_at _ _ _ => first [exact TL | rewrite ES; exact TL]
| |- fill_at _ (_ + 1) _ _ => exact SHpre
| |- fill_at _ _ _ _ => first [exact SHsuf | rewrite ES; exact SHsuf]
end.
all: try assumption.
all: try reflexivity.
all: try (generalize N KR B1 LO BOT STK3 POS; clear; intros; unfold AMALLOC_STACK in *; lia).
all: try exact HFKp.
all: match goal with |- ?G => idtac "REMS" G end. }
exact PRES.
Qed. Local Ltac2 Set LiaHints.tbl := fun () => "".
End S.
End CANSEC1.
